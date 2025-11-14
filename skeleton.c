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
char computeNextMoveForTruck(int truckId, int currentTurn);
void decidePickDropForTruck(int truckId, int currentTurn);
void writeDecisionsToShared(int currentTurn);

// ---- Authorization guessing ----
// for now: naive loop guessing a fixed dummy string of proper length
// (we can refine later)
void setTargetTruckForSolver(int solverId, int truckId);
void obtainAuthStringForTruck(int truckId, int solverId, int requiredLen);
void fillAuthStringsForMovingTrucks(int currentTurn);

// ---- Turn control ----
int sendTurnReady();
int mainLoop();

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

