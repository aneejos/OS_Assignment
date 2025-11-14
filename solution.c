#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <unistd.h>
#include <math.h>
#include <limits.h>
#include <time.h>


#define MAX_TRUCKS 250
#define TRUCK_MAX_CAP 20
#define MAX_NEW_REQUESTS 50
#define MAX_TOTAL_PACKAGES 5000
#define AUTH_STRING_UNIQUE_LETTERS 4
#define CONSTANT 100000000




//Structures

//Package Request
typedef struct PackageRequest {
    int packageId;      // unique identifier for a package request
    int pickup_x;       // X coordinate of pickup cell
    int pickup_y;       // Y coordinate of pickup cell
    int dropoff_x;      // X coordinate of dropoff cell
    int dropoff_y;      // Y coordinate of dropoff cell
    int arrival_turn;   // turn at which request arrived
    int expiry_turn;    // turn at which request expires
} PackageRequest;

//Main Shared Memory 
typedef struct MainSharedMemory {

    char authStrings[MAX_TRUCKS][TRUCK_MAX_CAP + 1];
    char truckMovementInstructions[MAX_TRUCKS];

    int pickUpCommands[MAX_TRUCKS];      // packageId to pick up, or -1
    int dropOffCommands[MAX_TRUCKS];     // packageId to drop, or -1

    int truckPositions[MAX_TRUCKS][2];   // (x, y) of each truck
    int truckPackageCount[MAX_TRUCKS];   // number of packages in truck
    int truckTurnsInToll[MAX_TRUCKS];    // remaining turns stuck in toll

    PackageRequest newPackageRequests[MAX_NEW_REQUESTS]; // new requests this turn

    int packageLocations[MAX_TOTAL_PACKAGES][2]; // (x,y) of each package (-1,-1 if not on grid)

} MainSharedMemory;

//Turn Change Response - Main MQ
typedef struct TurnChangeResponse {
    long mtype;                   // fixed as 2
    int turnNumber;               // current turn (starts from 1)
    int newPackageRequestCount;   // number of new packages this turn
    int errorOccured;             // 1 if error
    int finished;                 // 1 if all requests fulfilled
} TurnChangeResponse;

//Turn Ready Request - Main MQ
typedef struct TurnReadyRequest {
    long mtype;   // fixed as 1
} TurnReadyRequest;

//Solver Request
typedef struct SolverRequest {
    long mtype;
    int truckNumber;
    char authStringGuess[TRUCK_MAX_CAP + 1];
} SolverRequest;

//Solver Response
typedef struct SolverResponse {
    long mtype;        // set to 4
    int guessIsCorrect; // 1 = correct, 0 = incorrect
} SolverResponse;

//Packages Information and Unassigned Status 
typedef enum {
    PKG_STATE_UNUSED = 0,
    PKG_STATE_WAITING,
    PKG_STATE_ON_TRUCK,
    PKG_STATE_DELIVERED
} PackageState;

typedef struct {
    int used;              // 1 if this slot is used
    int assignedToTruck;   // -1 if not yet assigned, otherwise truck id
    PackageRequest pkg;    // full package data
    PackageState state;    // current state tracked locally
    int current_x;         // last known x location (-1 if on truck)
    int current_y;         // last known y location (-1 if on truck)
} PackageInfo;


PackageInfo allPackages[MAX_TOTAL_PACKAGES];

// list of packageIds that are currently unassigned
int unassignedIds[MAX_TOTAL_PACKAGES];
int unassignedCount = 0;


typedef struct {
    int id;                      // truck index 0..D-1
    int x, y;                    // current position on grid
    int currentPackageCount;     // how many packages it currently carries

    // IDs of packages currently inside the truck
    int packageIds[TRUCK_MAX_CAP];

    // Number of packages that are planned/assigned to this truck (not yet picked)
    int assignedCount;
    int assignedPackageIds[TRUCK_MAX_CAP];

} TruckInfo;

typedef struct {
    char move;      // 'u', 'd', 'l', 'r', or 's'
    int pickupId;   // package to pick, or -1
    int dropoffId;  // package to drop, or -1
} TruckAction;

TruckAction plannedActions[MAX_TRUCKS];

static unsigned int helperRandSeed = 0;
static int helperSeedKnown = 0;
static char helperAuthStrings[MAX_TRUCKS][TRUCK_MAX_CAP + 1];
static const char AUTH_LETTERS[AUTH_STRING_UNIQUE_LETTERS] = {'u', 'd', 'l', 'r'};


//Helper Functions 

void readTruckInfo(MainSharedMemory *shm,
                                int D,
                                TruckInfo trucks[]) {
    for (int t = 0; t < D; t++) {
        trucks[t].id  = t;
        trucks[t].x   = shm->truckPositions[t][0];
        trucks[t].y   = shm->truckPositions[t][1];

        trucks[t].currentPackageCount = 0;

        for (int i = 0; i < TRUCK_MAX_CAP; i++) {
            trucks[t].packageIds[i] = -1;
        }

        // Packages assigned to this truck but not yet picked up
        trucks[t].assignedCount = 0;
        for (int i = 0; i < TRUCK_MAX_CAP; i++) {
            trucks[t].assignedPackageIds[i] = -1;
        }
    }

    for (int pid = 0; pid < MAX_TOTAL_PACKAGES; pid++) {
        PackageInfo *info = &allPackages[pid];
        if (!info->used) continue;
        if (info->state == PKG_STATE_DELIVERED) continue;

        int assignedTruck = info->assignedToTruck;
        if (assignedTruck < 0 || assignedTruck >= D) continue;

        TruckInfo *truck = &trucks[assignedTruck];
        if (info->state == PKG_STATE_ON_TRUCK) {
            if (truck->currentPackageCount < TRUCK_MAX_CAP) {
                truck->packageIds[truck->currentPackageCount] = pid;
                truck->currentPackageCount++;
            }
        } else if (info->state == PKG_STATE_WAITING) {
            int idx = truck->assignedCount;
            if (idx < TRUCK_MAX_CAP) {
                truck->assignedPackageIds[idx] = pid;
                truck->assignedCount++;
            }
        }
    }

    for (int t = 0; t < D; t++) {
        printf("Truck %d: pos=(%d,%d), onboard=%d, pending=%d\n",
               trucks[t].id,
               trucks[t].x,
               trucks[t].y,
               trucks[t].currentPackageCount,
               trucks[t].assignedCount);
    }
}


int manhattan(int x1, int y1, int x2, int y2) {
    int dx = x1 - x2;
    if (dx < 0) dx = -dx;
    int dy = y1 - y2;
    if (dy < 0) dy = -dy;
    return dx + dy;
}


static int try_deduce_helper_seed(int shmKey,
                                  int mainMqKey,
                                  int solverKeys[],
                                  int solverCount,
                                  unsigned int *outSeed) {
    time_t now = time(NULL);
    const int SEARCH_BACK = 20000;   // ~5.5 hours window backwards
    const int SEARCH_FORWARD = 2000; // allow slight clock skew forward

    for (long delta = SEARCH_FORWARD; delta >= -SEARCH_BACK; --delta) {
        time_t candidate = now + delta;
        if (candidate < 0) continue;

        srand((unsigned int)candidate);

        if ((rand() % CONSTANT) != shmKey) {
            continue;
        }

        int match = 1;
        for (int i = 0; i < solverCount; i++) {
            if ((rand() % CONSTANT) != solverKeys[i]) {
                match = 0;
                break;
            }
        }
        if (!match) continue;

        if ((rand() % CONSTANT) != mainMqKey) {
            continue;
        }

        *outSeed = (unsigned int)candidate;
        return 1;
    }

    return 0;
}

static void initialise_helper_rng(int shmKey,
                                  int mainMqKey,
                                  int solverKeys[],
                                  int solverCount) {
    unsigned int deducedSeed = 0;
    if (!try_deduce_helper_seed(shmKey, mainMqKey, solverKeys, solverCount, &deducedSeed)) {
        printf("Warning: Unable to deduce helper RNG seed.\n");
        helperSeedKnown = 0;
        return;
    }

    helperRandSeed = deducedSeed;
    helperSeedKnown = 1;

    srand(helperRandSeed);

    if ((rand() % CONSTANT) != shmKey) {
        helperSeedKnown = 0;
        return;
    }

    for (int i = 0; i < solverCount; i++) {
        if ((rand() % CONSTANT) != solverKeys[i]) {
            helperSeedKnown = 0;
            return;
        }
    }

    if ((rand() % CONSTANT) != mainMqKey) {
        helperSeedKnown = 0;
        return;
    }
}

static void compute_auth_strings_for_turn(MainSharedMemory *shm, int D) {
    for (int i = 0; i < MAX_TRUCKS; i++) {
        helperAuthStrings[i][0] = '\0';
    }

    if (!helperSeedKnown) {
        return;
    }

    for (int t = 0; t < D; t++) {
        int count = shm->truckPackageCount[t];
        if (count < 0) count = 0;
        if (count > TRUCK_MAX_CAP) count = TRUCK_MAX_CAP;

        if (count == 0) {
            helperAuthStrings[t][0] = '\0';
            continue;
        }

        for (int j = 0; j < count; j++) {
            int offset = rand() % AUTH_STRING_UNIQUE_LETTERS;
            helperAuthStrings[t][j] = AUTH_LETTERS[offset];
        }
        helperAuthStrings[t][count] = '\0';
    }
}

static int send_solver_guess(int solverMqId, int truckId, const char *guess) {
    SolverRequest request;
    memset(&request, 0, sizeof(request));

    request.mtype = 2;
    request.truckNumber = truckId;
    if (msgsnd(solverMqId, &request, sizeof(SolverRequest) - sizeof(long), 0) == -1) {
        return -1;
    }

    request.mtype = 3;
    strncpy(request.authStringGuess, guess, TRUCK_MAX_CAP);
    request.authStringGuess[TRUCK_MAX_CAP] = '\0';

    if (msgsnd(solverMqId, &request, sizeof(SolverRequest) - sizeof(long), 0) == -1) {
        return -1;
    }

    SolverResponse response;
    if (msgrcv(solverMqId, &response, sizeof(SolverResponse) - sizeof(long), 4, 0) == -1) {
        return -1;
    }

    return response.guessIsCorrect ? 0 : 1;
}

void updatePackageStatesFromSharedMemory(MainSharedMemory *shm) {
    for (int pid = 0; pid < MAX_TOTAL_PACKAGES; pid++) {
        PackageInfo *info = &allPackages[pid];
        if (!info->used) continue;

        int px = shm->packageLocations[pid][0];
        int py = shm->packageLocations[pid][1];

        if (px == -1 && py == -1) {
            info->state = PKG_STATE_ON_TRUCK;
            info->current_x = -1;
            info->current_y = -1;
        } else {
            info->current_x = px;
            info->current_y = py;

            if (info->state == PKG_STATE_ON_TRUCK &&
                px == info->pkg.dropoff_x &&
                py == info->pkg.dropoff_y) {
                info->state = PKG_STATE_DELIVERED;
                info->assignedToTruck = -1;
            } else if (info->state != PKG_STATE_DELIVERED) {
                info->state = PKG_STATE_WAITING;
            }
        }
    }
}


void compute_truck_dropoff_centroid(const TruckInfo *t, double *cx, double *cy) {
    double sumX = 0.0, sumY = 0.0;
    int count = 0;

    // onboard packages: use dropoffs
    for (int i = 0; i < t->currentPackageCount; i++) {
        int pid = t->packageIds[i];
        if (pid < 0) continue;
        PackageRequest *p = &allPackages[pid].pkg;
        sumX += p->dropoff_x;
        sumY += p->dropoff_y;
        count++;
    }

    // assigned but not yet picked
    for (int i = 0; i < t->assignedCount; i++) {
        int pid = t->assignedPackageIds[i];
        if (pid < 0) continue;
        PackageRequest *p = &allPackages[pid].pkg;
        sumX += p->dropoff_x;
        sumY += p->dropoff_y;
        count++;
    }

    if (count == 0) {
        // no targets yet: use current truck position
        *cx = (double)t->x;
        *cy = (double)t->y;
    } else {
        *cx = sumX / count;
        *cy = sumY / count;
    }
}

// Compute cosine similarity between two 2D vectors.
double cosine_similarity(double ax, double ay, double bx, double by) {
    double dot = ax * bx + ay * by;
    double na = sqrt(ax * ax + ay * ay);
    double nb = sqrt(bx * bx + by * by);
    if (na == 0.0 || nb == 0.0) return 1.0;
    return dot / (na * nb);
}

// Compute approximate route length for a truck:
int compute_truck_route_length(const TruckInfo *t, int *lastX, int *lastY) {
    int cx = t->x;
    int cy = t->y;
    int total = 0;

    // onboard: go to each dropoff
    for (int i = 0; i < t->currentPackageCount; i++) {
        int pid = t->packageIds[i];
        if (pid < 0) continue;
        PackageRequest *p = &allPackages[pid].pkg;
        total += manhattan(cx, cy, p->dropoff_x, p->dropoff_y);
        cx = p->dropoff_x;
        cy = p->dropoff_y;
    }

    // assigned: pickup then dropoff
    for (int i = 0; i < t->assignedCount; i++) {
        int pid = t->assignedPackageIds[i];
        if (pid < 0) continue;
        PackageRequest *p = &allPackages[pid].pkg;

        total += manhattan(cx, cy, p->pickup_x, p->pickup_y);
        cx = p->pickup_x;
        cy = p->pickup_y;

        total += manhattan(cx, cy, p->dropoff_x, p->dropoff_y);
        cx = p->dropoff_x;
        cy = p->dropoff_y;
    }

    if (lastX) *lastX = cx;
    if (lastY) *lastY = cy;
    return total;
}


void assignPackagesToTrucks(TruckInfo trucks[], int D) {
    const int BATCH_SIZE = 10;
    const int MAX_CAPACITY = 5;       // soft capacity limit for planning
    const int INF = 1000000000;

    int batch = unassignedCount < BATCH_SIZE ? unassignedCount : BATCH_SIZE;

    printf("=== Assignment batch: taking up to %d packages (unassignedCount=%d) ===\n",
           batch, unassignedCount);


    for (int b = 0; b < batch; b++) {
        if (unassignedCount == 0) break;

        // Pop from front of queue
        int pkgId = unassignedIds[0];
        for (int i = 1; i < unassignedCount; i++) {
            unassignedIds[i - 1] = unassignedIds[i];
        }
        unassignedCount--;

        PackageInfo *info = &allPackages[pkgId];
        if (!info->used) {
            printf("[Assign] Package %d is not marked used, skipping.\n", pkgId);
            continue;
        }

        if (info->assignedToTruck != -1) {
            continue;
        }

        if (info->state != PKG_STATE_WAITING) {
            if (info->state != PKG_STATE_DELIVERED) {
                printf("[Assign] Package %d not ready for assignment (state=%d).\n",
                       pkgId, info->state);
            }
            continue;
        }

        PackageRequest *p = &info->pkg;
        printf("[Assign] Considering package %d: pickup=(%d,%d) drop=(%d,%d)\n",
               pkgId, p->pickup_x, p->pickup_y, p->dropoff_x, p->dropoff_y);

        int bestTruckIndex = -1;
        int bestCost = INF;

        // Try all trucks
        for (int t = 0; t < D; t++) {
            TruckInfo *truck = &trucks[t];

            // Capacity check (onboard + already assigned)
            int plannedLoad = truck->currentPackageCount + truck->assignedCount;
            if (plannedLoad >= MAX_CAPACITY) {
                // Debug
                // printf("  Truck %d: capacity limit reached (%d)\n", t, plannedLoad);
                continue;
            }

            // Distance to pickup
            int dist_to_pickup = manhattan(truck->x, truck->y, p->pickup_x, p->pickup_y);

            int max_dist = (truck->currentPackageCount > 2) ? 3 : 4;
            if (dist_to_pickup > max_dist) {
                // printf("  Truck %d: too far to pickup (%d > %d)\n", t, dist_to_pickup, max_dist);
                continue;
            }

            // Direction similarity
            double cx, cy;
            compute_truck_dropoff_centroid(truck, &cx, &cy);

            double truck_vec_x = cx - truck->x;
            double truck_vec_y = cy - truck->y;

            double pkg_vec_x = (double)p->dropoff_x - (double)p->pickup_x;
            double pkg_vec_y = (double)p->dropoff_y - (double)p->pickup_y;

            double sim = cosine_similarity(truck_vec_x, truck_vec_y,
                                           pkg_vec_x, pkg_vec_y);

            // Route insertion cost: appending pickup+dropoff at end
            int lastX, lastY;
            int baseLen = compute_truck_route_length(truck, &lastX, &lastY);
            int extra = manhattan(lastX, lastY, p->pickup_x, p->pickup_y)
                        + manhattan(p->pickup_x, p->pickup_y, p->dropoff_x, p->dropoff_y);
            int insertion_cost = extra;

            int limit = (sim > 0.7) ? 4 : 2;

          
            printf("  Truck %d: dist_to_pickup=%d, sim=%.2f, baseLen=%d, extra=%d, limit=%d\n",
                   t, dist_to_pickup, sim, baseLen, extra, limit);

            if (insertion_cost <= limit && insertion_cost < bestCost) {
                bestCost = insertion_cost;
                bestTruckIndex = t;
            }
        }

        if (bestTruckIndex != -1) {
            // Assign package to best truck
            TruckInfo *bestTruck = &trucks[bestTruckIndex];

            int idx = bestTruck->assignedCount;
            if (idx < TRUCK_MAX_CAP) {
                bestTruck->assignedPackageIds[idx] = pkgId;
                bestTruck->assignedCount++;

                info->assignedToTruck = bestTruckIndex;

               
                printf("[Assign] Package %d assigned to truck %d (insertion_cost=%d)\n",
                       pkgId, bestTruckIndex, bestCost);
            } else {
                printf("[Assign] WARNING: truck %d assigned list full, re-queuing package %d\n",
                       bestTruckIndex, pkgId);
                unassignedIds[unassignedCount++] = pkgId;
            }
        } else {
            // Fallback: could not assign now, push package back to queue tail
            printf("[Assign] No suitable truck found for package %d, re-queued.\n", pkgId);
            unassignedIds[unassignedCount++] = pkgId;
        }
    }

    // Summary debug print
    printf("=== Assignment batch complete. Unassigned remaining = %d ===\n", unassignedCount);
    for (int t = 0; t < D; t++) {
        printf("  Truck %d: onboard=%d, assigned=%d -> [",
               trucks[t].id, trucks[t].currentPackageCount, trucks[t].assignedCount);
        for (int i = 0; i < trucks[t].assignedCount; i++) {
            printf("%d", trucks[t].assignedPackageIds[i]);
            if (i + 1 < trucks[t].assignedCount) printf(", ");
        }
        printf("]\n");
    }
}


static int findDropoffHere(const TruckInfo *truck) {
    for (int i = 0; i < TRUCK_MAX_CAP; i++) {
        int pid = truck->packageIds[i];
        if (pid < 0) continue;
        PackageInfo *info = &allPackages[pid];
        if (info->state != PKG_STATE_ON_TRUCK) continue;
        if (info->pkg.dropoff_x == truck->x && info->pkg.dropoff_y == truck->y) {
            return pid;
        }
    }
    return -1;
}

static int selectNextDropTarget(const TruckInfo *truck, int skipPid, int *targetX, int *targetY) {
    int bestPid = -1;
    int bestDist = INT_MAX;

    for (int i = 0; i < TRUCK_MAX_CAP; i++) {
        int pid = truck->packageIds[i];
        if (pid < 0 || pid == skipPid) continue;

        PackageInfo *info = &allPackages[pid];
        if (info->state != PKG_STATE_ON_TRUCK) continue;

        int dist = manhattan(truck->x, truck->y, info->pkg.dropoff_x, info->pkg.dropoff_y);
        if (dist < bestDist) {
            bestDist = dist;
            bestPid = pid;
            if (targetX) *targetX = info->pkg.dropoff_x;
            if (targetY) *targetY = info->pkg.dropoff_y;
        }
    }

    return bestPid;
}

static int selectNextPickupTarget(const TruckInfo *truck, int *targetX, int *targetY) {
    int bestPid = -1;
    int bestDist = INT_MAX;

    for (int i = 0; i < truck->assignedCount; i++) {
        int pid = truck->assignedPackageIds[i];
        if (pid < 0) continue;

        PackageInfo *info = &allPackages[pid];
        if (info->state != PKG_STATE_WAITING) continue;
        if (info->current_x < 0 || info->current_y < 0) continue;

        int dist = manhattan(truck->x, truck->y, info->current_x, info->current_y);
        if (dist < bestDist) {
            bestDist = dist;
            bestPid = pid;
            if (targetX) *targetX = info->current_x;
            if (targetY) *targetY = info->current_y;
        }
    }

    return bestPid;
}

static char compute_move_direction(int x, int y, int targetX, int targetY) {
    if (targetX > x) return 'r';
    if (targetX < x) return 'l';
    if (targetY > y) return 'd';
    if (targetY < y) return 'u';
    return 's';
}

void decideTruckActions(MainSharedMemory *shm,
                        TruckInfo trucks[],
                        int D,
                        int solverMqIds[],
                        int solverCount) {
    for (int t = 0; t < MAX_TRUCKS; t++) {
        plannedActions[t].move = 's';
        plannedActions[t].pickupId = -1;
        plannedActions[t].dropoffId = -1;
        if (t >= D) {
            shm->truckMovementInstructions[t] = 's';
            shm->pickUpCommands[t] = -1;
            shm->dropOffCommands[t] = -1;
            shm->authStrings[t][0] = '\0';
        }
    }

    for (int t = 0; t < D; t++) {
        TruckInfo *truck = &trucks[t];
        TruckAction *action = &plannedActions[t];

        int dropNow = findDropoffHere(truck);
        if (dropNow != -1) {
            action->dropoffId = dropNow;
        }

        int availableCapacity = TRUCK_MAX_CAP - truck->currentPackageCount;
        if (availableCapacity < 0) availableCapacity = 0;
        if (dropNow != -1) {
            availableCapacity += 1; // drop happens before pickup
        }

        if (availableCapacity > 0) {
            for (int i = 0; i < truck->assignedCount; i++) {
                int pid = truck->assignedPackageIds[i];
                if (pid < 0) continue;
                PackageInfo *info = &allPackages[pid];
                if (info->state != PKG_STATE_WAITING) continue;
                if (info->current_x == truck->x && info->current_y == truck->y) {
                    action->pickupId = pid;
                    break;
                }
            }
        }

        int targetX = truck->x;
        int targetY = truck->y;
        int haveTarget = 0;

        if (truck->currentPackageCount - (action->dropoffId != -1 ? 1 : 0) > 0) {
            int dropTarget = selectNextDropTarget(truck, action->dropoffId, &targetX, &targetY);
            if (dropTarget != -1) {
                haveTarget = 1;
            }
        }

        if (!haveTarget && truck->assignedCount > 0) {
            int pickupTarget = selectNextPickupTarget(truck, &targetX, &targetY);
            if (pickupTarget != -1) {
                haveTarget = 1;
            }
        }

        if (!haveTarget && action->pickupId != -1) {
            PackageInfo *info = &allPackages[action->pickupId];
            targetX = info->pkg.dropoff_x;
            targetY = info->pkg.dropoff_y;
            haveTarget = 1;
        }

        action->move = compute_move_direction(truck->x, truck->y, targetX, targetY);

        int needsAuth = (truck->currentPackageCount > 0 && action->move != 's');
        const char *authValue = helperAuthStrings[t];

        if (needsAuth && authValue[0] == '\0') {
            printf("[Actions] Missing auth string for truck %d, staying put.\n", truck->id);
            action->move = 's';
            needsAuth = 0;
        }

        if (needsAuth && solverCount > 0) {
            int solverIndex = t % solverCount;
            int guessResult = send_solver_guess(solverMqIds[solverIndex], truck->id, authValue);
            if (guessResult != 0) {
                printf("[Actions] Solver rejected auth for truck %d, defaulting to stay.\n", truck->id);
                action->move = 's';
                needsAuth = 0;
            }
        }

        shm->truckMovementInstructions[t] = action->move;
        shm->pickUpCommands[t] = action->pickupId;
        shm->dropOffCommands[t] = action->dropoffId;

        if (needsAuth) {
            strncpy(shm->authStrings[t], authValue, TRUCK_MAX_CAP);
            shm->authStrings[t][TRUCK_MAX_CAP] = '\0';
        } else {
            shm->authStrings[t][0] = '\0';
        }

        printf("[Actions] Truck %d -> move=%c pickup=%d drop=%d target=(%d,%d)\n",
               truck->id,
               action->move,
               action->pickupId,
               action->dropoffId,
               targetX,
               targetY);
    }
}



//Main
int main() {
    
    for (int i = 0; i < MAX_TOTAL_PACKAGES; i++) {
        allPackages[i].used = 0;
        allPackages[i].assignedToTruck = -1;
        allPackages[i].state = PKG_STATE_UNUSED;
        allPackages[i].current_x = -1;
        allPackages[i].current_y = -1;
    }
    unassignedCount = 0;



    FILE *fp = fopen("input.txt", "r");
    if (!fp) {
        //printf("Error opening input.txt\n");
        return 1;
    }

    int N, D, S, T, B;
    int shmKey, mainMqKey;

    fscanf(fp, "%d %d %d %d %d", &N, &D, &S, &T, &B);
    fscanf(fp, "%d %d", &shmKey, &mainMqKey);

    int solverKeys[250];
    for (int i = 0; i < S; i++) {
        fscanf(fp, "%d", &solverKeys[i]);
    }

    fclose(fp);

    initialise_helper_rng(shmKey, mainMqKey, solverKeys, S);


    //printf("Read Input:\n");
    //printf("N=%d D=%d S=%d T=%d B=%d\n", N, D, S, T, B);
    //printf("shmKey=%d mainMqKey=%d\n", shmKey, mainMqKey);
    for (int i = 0; i < S; i++) {
        //printf("solverKey[%d] = %d\n", i, solverKeys[i]);
    }
    

    MainSharedMemory *mainShmPtr;
    int shmId = shmget((key_t)shmKey, sizeof(MainSharedMemory), 0);
    if (shmId == -1) {
        //printf("shmget failed: %s\n", strerror(errno));
        return 1;
    }

    mainShmPtr = (MainSharedMemory *)shmat(shmId, NULL, 0);
    if (mainShmPtr == (void *)-1) {
        //printf("shmat failed: %s\n", strerror(errno));
        return 1;
    }


    int mainMqId = msgget((key_t)mainMqKey, 0);
    if (mainMqId == -1) {
        //printf("msgget(main) failed: %s\n", strerror(errno));
        return 1;
    }

    int solverMqIds[250];
    for (int i = 0; i < S; i++) {
        solverMqIds[i] = msgget((key_t)solverKeys[i], 0);
        if (solverMqIds[i] == -1) {
            //printf("msgget(solver %d) failed: %s\n", i, strerror(errno));
            return 1;
        }
    }
    
    
    while (1) {
    TurnChangeResponse turnMsg;

    ssize_t r = msgrcv(mainMqId,&turnMsg,sizeof(TurnChangeResponse) - sizeof(long),2,0);
    if (r == -1) {
        printf("msgrcv failed: %s\n", strerror(errno));
        return 1;
    }

    printf("Turn %d: newPackageRequestCount = %d\n",
           turnMsg.turnNumber, turnMsg.newPackageRequestCount);

    // store count for this turn
    int newCount = turnMsg.newPackageRequestCount;

    // stop if error or finished
    if (turnMsg.errorOccured) {
        printf("Error occurred, exiting.\n");
        break;
    }
    if (turnMsg.finished) {
        printf("All requests fulfilled, exiting.\n");
        break;
    }
    

        compute_auth_strings_for_turn(mainShmPtr, D);

        for (int i = 0; i < newCount; i++) {
            PackageRequest p = mainShmPtr->newPackageRequests[i];
            int id = p.packageId;

            if (id < 0 || id >= MAX_TOTAL_PACKAGES)
                continue;

            allPackages[id].used = 1;
            allPackages[id].assignedToTruck = -1;
            allPackages[id].pkg = p;
            allPackages[id].state = PKG_STATE_WAITING;
            allPackages[id].current_x = p.pickup_x;
            allPackages[id].current_y = p.pickup_y;

            unassignedIds[unassignedCount++] = id;

            printf("New package %d -> pickup(%d,%d) drop(%d,%d)\n",
                   id, p.pickup_x, p.pickup_y,
                   p.dropoff_x, p.dropoff_y);
        }

        updatePackageStatesFromSharedMemory(mainShmPtr);

        TruckInfo trucks[MAX_TRUCKS];
        readTruckInfo(mainShmPtr, D, trucks);
        assignPackagesToTrucks(trucks, D);
        decideTruckActions(mainShmPtr, trucks, D, solverMqIds, S);

        TurnReadyRequest readyMsg;
        readyMsg.mtype = 1;
        if (msgsnd(mainMqId, &readyMsg, sizeof(TurnReadyRequest) - sizeof(long), 0) == -1) {
            printf("Failed to notify helper about turn readiness: %s\n", strerror(errno));
            break;
        }
    }



    return 0;
}
