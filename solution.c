#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <sys/types.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <unistd.h>
#include<math.h>


#define MAX_TRUCKS 250
#define TRUCK_MAX_CAP 20
#define MAX_NEW_REQUESTS 50
#define MAX_TOTAL_PACKAGES 5000




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
typedef struct {
    int used;              // 1 if this slot is used
    int assignedToTruck;   // -1 if not yet assigned, otherwise truck id
    PackageRequest pkg;    // full package data
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

//Helper Functions 

void readTruckInfo(MainSharedMemory *shm,
                                int D,
                                TruckInfo trucks[]) {
    for (int t = 0; t < D; t++) {
        trucks[t].id  = t;
        trucks[t].x   = shm->truckPositions[t][0];
        trucks[t].y   = shm->truckPositions[t][1];

        trucks[t].currentPackageCount = shm->truckPackageCount[t];

        for (int i = 0; i < TRUCK_MAX_CAP; i++) {
            trucks[t].packageIds[i] = -1;
        }

        // Packages assigned to this truck but not yet picked up
        trucks[t].assignedCount = 0;
        for (int i = 0; i < TRUCK_MAX_CAP; i++) {
            trucks[t].assignedPackageIds[i] = -1;
        }
        
        printf("Truck %d: pos=(%d,%d), currentPackageCount=%d\n",
               trucks[t].id,
               trucks[t].x,
               trucks[t].y,
               trucks[t].currentPackageCount);
        }
    }


int manhattan(int x1, int y1, int x2, int y2) {
    int dx = x1 - x2;
    if (dx < 0) dx = -dx;
    int dy = y1 - y2;
    if (dy < 0) dy = -dy;
    return dx + dy;
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



//Main
int main() {
    
    for (int i = 0; i < MAX_TOTAL_PACKAGES; i++) {
    allPackages[i].used = 0;
    allPackages[i].assignedToTruck = -1;
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
    

    for (int i = 0; i < newCount; i++) {
    PackageRequest p = mainShmPtr->newPackageRequests[i];
    int id = p.packageId;

    if (id < 0 || id >= MAX_TOTAL_PACKAGES)
        continue;

    allPackages[id].used = 1;
    allPackages[id].assignedToTruck = -1;
    allPackages[id].pkg = p;

    unassignedIds[unassignedCount++] = id;

    printf("New package %d -> pickup(%d,%d) drop(%d,%d)\n",
           id, p.pickup_x, p.pickup_y,
           p.dropoff_x, p.dropoff_y);
        }
        
    TruckInfo trucks[MAX_TRUCKS];
    readTruckInfo(mainShmPtr, D, trucks);
    assignPackagesToTrucks(trucks, D);


   }
   
   

    return 0;
}
