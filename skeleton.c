// =========================
//  Includes & Constants
// =========================
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <unistd.h>

#define MAX_TRUCKS          250
#define TRUCK_MAX_CAP       20
#define MAX_NEW_REQUESTS    50
#define MAX_TOTAL_PACKAGES  5000

// Directions
#define MOVE_LEFT  'l'
#define MOVE_RIGHT 'r'
#define MOVE_UP    'u'
#define MOVE_DOWN  'd'
#define MOVE_STAY  's'

// =========================
//  REGION 1: STRUCTURES
// =========================

// ---- Given by problem ----
typedef struct PackageRequest {
    int packageId;
    int pickup_x;
    int pickup_y;
    int dropoff_x;
    int dropoff_y;
    int arrival_turn;
    int expiry_turn;
} PackageRequest;

typedef struct MainSharedMemory {
    char authStrings[MAX_TRUCKS][TRUCK_MAX_CAP + 1];
    char truckMovementInstructions[MAX_TRUCKS];

    int pickUpCommands[MAX_TRUCKS];     // packageId or -1
    int dropOffCommands[MAX_TRUCKS];    // packageId or -1

    int truckPositions[MAX_TRUCKS][2];  // (x, y)
    int truckPackageCount[MAX_TRUCKS];  // number of packages in truck
    int truckTurnsInToll[MAX_TRUCKS];   // ignored for now

    PackageRequest newPackageRequests[MAX_NEW_REQUESTS];

    int packageLocations[MAX_TOTAL_PACKAGES][2]; // (x,y) or (-1,-1)
} MainSharedMemory;

typedef struct TurnChangeResponse {
    long mtype;                 // 2
    int turnNumber;
    int newPackageRequestCount;
    int errorOccured;
    int finished;
} TurnChangeResponse;

typedef struct TurnReadyRequest {
    long mtype;                 // 1
} TurnReadyRequest;

typedef struct SolverRequest {
    long mtype;                 // 2 or 3
    int truckNumber;            // used when mtype = 2
    char authStringGuess[TRUCK_MAX_CAP + 1];
} SolverRequest;

typedef struct SolverResponse {
    long mtype;                 // 4
    int guessIsCorrect;         // 1 or 0
} SolverResponse;

// ---- Our additional structures ----

// Local per-package state
typedef struct PackageInfo {
    int packageId;
    int pickup_x;
    int pickup_y;
    int dropoff_x;
    int dropoff_y;
    int arrival_turn;
    int expiry_turn;

    int assignedTruckId;    // -1 if unassigned
    int pickedUp;           // 0/1
    int delivered;          // 0/1

    int current_x;          // last known position (grid)
    int current_y;
} PackageInfo;

// Local per-truck state
typedef struct TruckInfo {
    int id;
    int x;
    int y;

    int onboardCount;
    int onboardPackageIds[TRUCK_MAX_CAP];

    int assignedCount;      // packages assigned but not yet picked up
    int assignedPackageIds[TRUCK_MAX_CAP];
} TruckInfo;

// Simple queue of package indices for "unassigned" packages
typedef struct PackageQueue {
    int indices[MAX_TOTAL_PACKAGES];
    int front;
    int rear;
    int size;
} PackageQueue;

// =========================
//  GLOBALS (basic version)
// =========================

static int N;          // grid size
static int D;          // number of trucks
static int S;          // number of solvers
static int T_last;     // last request turn
static int B;          // toll booths (ignored for now)

static key_t shmKey;
static key_t mainMqKey;
static key_t solverMqKeyBase;   // will be offset for each solver

static int shmId;
static int mainMqId;
static int solverMqIds[MAX_TRUCKS];  // up to D; we will only use S

static MainSharedMemory *mainShmPtr = NULL;
static TruckInfo trucks[MAX_TRUCKS];
static PackageInfo packages[MAX_TOTAL_PACKAGES];
static PackageQueue unassignedQueue;

// =========================
//  REGION 2: FUNCTIONS
// =========================

// ---- Helpers: queue & init ----
void initPackageQueue(PackageQueue *q)
{
    q->front = 0;
    q->rear = -1;
    q->size = 0;
};

int isPackageQueueEmpty(PackageQueue *q)
{
    return (q->size == 0);
};

void enqueuePackage(PackageQueue *q, int pkgIndex)
{
    if (q->size >= MAX_TOTAL_PACKAGES) {
        // queue overflow should never happen in valid test cases
        return;
    }
    q->rear = (q->rear + 1) % MAX_TOTAL_PACKAGES;
    q->indices[q->rear] = pkgIndex;
    q->size++;
};

int dequeuePackage(PackageQueue *q)
{
    if (q->size == 0) {
        return -1;
    }
    int val = q->indices[q->front];
    q->front = (q->front + 1) % MAX_TOTAL_PACKAGES;
    q->size--;
    return val;
};


void initLocalState()
{
    // --- Initialize unassigned queue ---
    initPackageQueue(&unassignedQueue);

    // --- Clear all package slots ---
    for (int i = 0; i < MAX_TOTAL_PACKAGES; i++) {
        packages[i].packageId = -1;
        packages[i].assignedTruckId = -1;
        packages[i].pickedUp = 0;
        packages[i].delivered = 0;
    }

    // --- Initialize trucks from shared memory initial state ---
    for (int t = 0; t < D; t++) {
        trucks[t].id = t;

        trucks[t].x = mainShmPtr->truckPositions[t][0];
        trucks[t].y = mainShmPtr->truckPositions[t][1];

        trucks[t].onboardCount = 0;
        trucks[t].assignedCount = 0;
    }

    // --- Set safe defaults in shared memory ---
    for (int t = 0; t < D; t++) {
        mainShmPtr->truckMovementInstructions[t] = MOVE_STAY;
        mainShmPtr->pickUpCommands[t] = -1;
        mainShmPtr->dropOffCommands[t] = -1;

        // Clear auth strings initially
        memset(mainShmPtr->authStrings[t], 0, TRUCK_MAX_CAP + 1);
    }
};

int findPackageSlotById(int packageId)
{
    if (packageId < 0) return -1;

    for (int i = 0; i < MAX_TOTAL_PACKAGES; i++) {
        if (packages[i].packageId == packageId) {
            return i;
        }
    }
    return -1;
}; // returns index or -1

// ---- Input & IPC setup ----
int readInputFile(const char *path)
{
    FILE *fp = fopen(path, "r");
    if (!fp) {
        fprintf(stderr, "Error opening %s: %s\n", path, strerror(errno));
        return 1;
    }

    if (fscanf(fp, "%d %d %d %d %d %d %d %d",
               &N, &D, &S, &T_last, &B,
               &shmKey, &mainMqKey, &solverMqKeyBase) != 8)
    {
        fprintf(stderr, "Invalid input.txt format\n");
        fclose(fp);
        return 1;
    }

    fclose(fp);
    return 0;
};

int setupSharedMemory()
{
    shmId = shmget((key_t)shmKey, sizeof(MainSharedMemory), 0);
    if (shmId == -1) {
        fprintf(stderr, "shmget failed: %s\n", strerror(errno));
        return 1;
    }

    mainShmPtr = (MainSharedMemory *) shmat(shmId, NULL, 0);
    if (mainShmPtr == (void *) -1) {
        fprintf(stderr, "shmat failed: %s\n", strerror(errno));
        return 1;
    }

    return 0;
};

int setupMainMessageQueue()
{
    mainMqId = msgget((key_t)mainMqKey, 0);
    if (mainMqId == -1) {
        fprintf(stderr, "msgget(mainMq) failed: %s\n", strerror(errno));
        return 1;
    }
    return 0;
};

int setupSolverMessageQueues()
{
    for (int i = 0; i < S; i++) {
        key_t k = (key_t)(solverMqKeyBase + i);

        int mqid = msgget(k, 0);     // queues are already created by helper
        if (mqid == -1) {
            fprintf(stderr, "msgget(solver %d) failed: %s\n", i, strerror(errno));
            return 1;
        }

        solverMqIds[i] = mqid;
    }

    return 0;
};

// ---- Turn loop helpers ----
int readTurnChange(TurnChangeResponse *resp)
{
    ssize_t r = msgrcv(mainMqId, resp, sizeof(TurnChangeResponse) - sizeof(long),
                       2, 0);
    if (r == -1) {
        fprintf(stderr, "msgrcv TurnChangeResponse failed: %s\n", strerror(errno));
        return 1;
    }
    return 0;
};

void ingestNewPackagesIntoQueue(int newCount, int currentTurn)
{
    for (int i = 0; i < newCount; i++) {

        PackageRequest *pr = &mainShmPtr->newPackageRequests[i];
        int pid = pr->packageId;

        int idx = findPackageSlotById(pid);

        if (idx == -1) {
            // Find a free slot
            for (int j = 0; j < MAX_TOTAL_PACKAGES; j++) {
                if (packages[j].packageId == -1) {
                    idx = j;
                    break;
                }
            }
        }

        if (idx == -1) {
            // should never happen in valid inputs
            continue;
        }

        packages[idx].packageId = pid;
        packages[idx].pickup_x  = pr->pickup_x;
        packages[idx].pickup_y  = pr->pickup_y;
        packages[idx].dropoff_x = pr->dropoff_x;
        packages[idx].dropoff_y = pr->dropoff_y;
        packages[idx].arrival_turn = pr->arrival_turn;
        packages[idx].expiry_turn  = pr->expiry_turn;

        packages[idx].assignedTruckId = -1;
        packages[idx].pickedUp = 0;
        packages[idx].delivered = 0;

        enqueuePackage(&unassignedQueue, idx);
    }
};

void syncTruckPositionsFromShared()
{
    for (int t = 0; t < D; t++) {
        trucks[t].x = mainShmPtr->truckPositions[t][0];
        trucks[t].y = mainShmPtr->truckPositions[t][1];
    }
};

// ---- Assignment algorithm (simple version) ----
// each truck picks one nearest unassigned package (greedy)
void assignPackagesSimple(int currentTurn)
{
    (void) currentTurn;  // unused for now; kept for future optimizations

    if (unassignedQueue.size == 0) {
        return;
    }

    for (int t = 0; t < D; t++) {
        TruckInfo *truck = &trucks[t];

        // One-package-at-a-time rule
        if (truck->onboardCount > 0 || truck->assignedCount > 0) {
            continue;
        }

        int bestPkgIdx = -1;
        int bestDist = 1000000000;  // effectively INF

        int qSize = unassignedQueue.size;
        int pos = unassignedQueue.front;

        for (int k = 0; k < qSize; k++) {
            int pkgIdx = unassignedQueue.indices[pos];
            pos = (pos + 1) % MAX_TOTAL_PACKAGES;

            if (pkgIdx < 0 || pkgIdx >= MAX_TOTAL_PACKAGES) {
                continue;
            }

            PackageInfo *pkg = &packages[pkgIdx];

            if (pkg->packageId == -1) {
                continue;
            }
            if (pkg->delivered) {
                continue;
            }
            if (pkg->assignedTruckId != -1) {
                continue;
            }

            int dist = abs(truck->x - pkg->pickup_x) +
                       abs(truck->y - pkg->pickup_y);

            if (dist < bestDist) {
                bestDist = dist;
                bestPkgIdx = pkgIdx;
            }
        }

        if (bestPkgIdx != -1) {
            PackageInfo *chosen = &packages[bestPkgIdx];

            chosen->assignedTruckId = t;

            truck->assignedCount = 1;
            truck->assignedPackageIds[0] = chosen->packageId;
        }
    }
};

// ---- Movement & decisions ----
static int getActivePackageIndexForTruck(int truckId)
{
    TruckInfo *truck = &trucks[truckId];

    // Prefer onboard package
    if (truck->onboardCount > 0) {
        int pkgId = truck->onboardPackageIds[0];
        int idx = findPackageSlotById(pkgId);
        if (idx != -1) return idx;
    }

    // Otherwise, assigned but not yet picked
    if (truck->assignedCount > 0) {
        int pkgId = truck->assignedPackageIds[0];
        int idx = findPackageSlotById(pkgId);
        if (idx != -1) return idx;
    }

    return -1;
};

char computeNextMoveForTruck(int truckId, int currentTurn)
{
    (void) currentTurn;  // reserved for future use

    TruckInfo *truck = &trucks[truckId];
    int pkgIdx = getActivePackageIndexForTruck(truckId);

    if (pkgIdx == -1) {
        return MOVE_STAY;
    }

    PackageInfo *pkg = &packages[pkgIdx];

    int target_x, target_y;

    if (pkg->pickedUp && !pkg->delivered) {
        target_x = pkg->dropoff_x;
        target_y = pkg->dropoff_y;
    } else {
        target_x = pkg->pickup_x;
        target_y = pkg->pickup_y;
    }

    if (truck->x < target_x) return MOVE_RIGHT;
    if (truck->x > target_x) return MOVE_LEFT;
    if (truck->y < target_y) return MOVE_DOWN;
    if (truck->y > target_y) return MOVE_UP;

    return MOVE_STAY;
};

void decidePickDropForTruck(int truckId, int currentTurn)
{
    (void) currentTurn;

    TruckInfo *truck = &trucks[truckId];

    mainShmPtr->pickUpCommands[truckId] = -1;
    mainShmPtr->dropOffCommands[truckId] = -1;

    int pkgIdx = getActivePackageIndexForTruck(truckId);
    if (pkgIdx == -1) {
        return;
    }

    PackageInfo *pkg = &packages[pkgIdx];

    // Pickup case
    if (!pkg->pickedUp && !pkg->delivered &&
        truck->x == pkg->pickup_x && truck->y == pkg->pickup_y)
    {
        mainShmPtr->pickUpCommands[truckId] = pkg->packageId;

        pkg->pickedUp = 1;
        pkg->assignedTruckId = truckId;

        truck->onboardCount = 1;
        truck->onboardPackageIds[0] = pkg->packageId;
        truck->assignedCount = 0;

        return;
    }

    // Dropoff case
    if (pkg->pickedUp && !pkg->delivered &&
        truck->x == pkg->dropoff_x && truck->y == pkg->dropoff_y)
    {
        mainShmPtr->dropOffCommands[truckId] = pkg->packageId;

        pkg->delivered = 1;
        pkg->assignedTruckId = -1;

        truck->onboardCount = 0;
        if (truck->onboardCount > 0) {
            truck->onboardPackageIds[0] = -1;
        }
    }
};
void writeDecisionsToShared(int currentTurn)
{
    for (int t = 0; t < D; t++) {
        decidePickDropForTruck(t, currentTurn);

        char move = computeNextMoveForTruck(t, currentTurn);
        mainShmPtr->truckMovementInstructions[t] = move;
    }
};

// ---- Authorization guessing ----
// for now: naive loop guessing a fixed dummy string of proper length
// (we can refine later)
void setTargetTruckForSolver(int solverId, int truckId)
{
    SolverRequest req;
    req.mtype = 2;        // specify truck for solver
    req.truckNumber = truckId;
    req.authStringGuess[0] = '\0';

    if (msgsnd(solverMqIds[solverId], &req,
               sizeof(SolverRequest) - sizeof(long), 0) == -1)
    {
        fprintf(stderr, "msgsnd setTargetTruck failed: %s\n", strerror(errno));
    }
};

void obtainAuthStringForTruck(int truckId, int solverId, int requiredLen)
{
    // For now only simple case: length = 1
    if (requiredLen != 1) {
        // Fallback: just fill with 'u'
        mainShmPtr->authStrings[truckId][0] = 'u';
        mainShmPtr->authStrings[truckId][1] = '\0';
        return;
    }

    const char candidates[4] = { 'u', 'd', 'l', 'r' };

    for (int i = 0; i < 4; i++) {

        SolverRequest req;
        req.mtype = 3;  // guess message
        req.truckNumber = truckId;

        req.authStringGuess[0] = candidates[i];
        req.authStringGuess[1] = '\0';

        // send guess
        if (msgsnd(solverMqIds[solverId], &req,
                   sizeof(SolverRequest) - sizeof(long), 0) == -1)
        {
            fprintf(stderr, "msgsnd guess failed: %s\n", strerror(errno));
            continue;
        }

        // wait for solver response
        SolverResponse resp;
        if (msgrcv(solverMqIds[solverId], &resp,
                   sizeof(SolverResponse) - sizeof(long),
                   4, 0) == -1)
        {
            fprintf(stderr, "msgrcv solver response failed: %s\n",
                    strerror(errno));
            continue;
        }

        if (resp.guessIsCorrect == 1) {
            // correct auth
            mainShmPtr->authStrings[truckId][0] = candidates[i];
            mainShmPtr->authStrings[truckId][1] = '\0';
            return;
        }
    }

    // If somehow none succeeded (should not happen)
    mainShmPtr->authStrings[truckId][0] = 'u';
    mainShmPtr->authStrings[truckId][1] = '\0';
};

void fillAuthStringsForMovingTrucks(int currentTurn)
{
    (void) currentTurn; // not needed for simple version

    for (int t = 0; t < D; t++) {

        char move = mainShmPtr->truckMovementInstructions[t];
        if (move == MOVE_STAY) {
            continue;   // no auth needed
        }

        int solverId = t % S;

        setTargetTruckForSolver(solverId, t);

        // Since only one package in our current version:
        int requiredLen = 1;

        obtainAuthStringForTruck(t, solverId, requiredLen);
    }
};

// ---- Turn control ----
int sendTurnReady()
{
    TurnReadyRequest req;
    req.mtype = 1;

    if (msgsnd(mainMqId, &req,
               sizeof(TurnReadyRequest) - sizeof(long), 0) == -1)
    {
        fprintf(stderr, "msgsnd TurnReady failed: %s\n", strerror(errno));
        return 1;
    }

    return 0;
};
int mainLoop()
{
    while (1) {

        // Step 1: Announce ready for next turn
        if (sendTurnReady() != 0) {
            return 1;
        }

        // Step 2: Receive turn-change info
        TurnChangeResponse resp;
        if (readTurnChange(&resp) != 0) {
            return 1;
        }

        int turn = resp.turnNumber;

        // End condition
        if (resp.finished == 1) {
            break;
        }

        // Step 3: Sync truck positions from shared memory
        syncTruckPositionsFromShared();

        // Step 4: Ingest new packages for this turn
        if (resp.newPackageRequestCount > 0) {
            ingestNewPackagesIntoQueue(resp.newPackageRequestCount, turn);
        }

        // Step 5: Assign packages (nearest-package single-assignment rule)
        assignPackagesSimple(turn);

        // Step 6: Determine movements + pickup/drop commands
        writeDecisionsToShared(turn);

        // Step 7: Fill authorization strings for moving trucks
        fillAuthStringsForMovingTrucks(turn);
    }

    return 0;
};

// =========================
//  REGION 3: MAIN
// =========================

int main(void) {
    if (readInputFile("input.txt") != 0) {
        fprintf(stderr, "Failed to read input.txt\n");
        return 1;
    }

    if (setupSharedMemory() != 0) {
        fprintf(stderr, "Failed to setup shared memory\n");
        return 1;
    }

    if (setupMainMessageQueue() != 0) {
        fprintf(stderr, "Failed to setup main message queue\n");
        return 1;
    }

    if (setupSolverMessageQueues() != 0) {
        fprintf(stderr, "Failed to setup solver message queues\n");
        return 1;
    }

    initLocalState();

    if (mainLoop() != 0) {
        fprintf(stderr, "Error inside main loop\n");
        return 1;
    }

    // detach shared memory on exit
    if (mainShmPtr != NULL) {
        shmdt(mainShmPtr);
    }

    return 0;
}

