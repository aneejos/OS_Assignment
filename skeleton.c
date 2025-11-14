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
void initPackageQueue(PackageQueue *q);
int  isPackageQueueEmpty(PackageQueue *q);
void enqueuePackage(PackageQueue *q, int pkgIndex);
int  dequeuePackage(PackageQueue *q);

void initLocalState();
int  findPackageSlotById(int packageId); // returns index or -1

// ---- Input & IPC setup ----
int readInputFile(const char *path);
int setupSharedMemory();
int setupMainMessageQueue();
int setupSolverMessageQueues();

// ---- Turn loop helpers ----
int readTurnChange(TurnChangeResponse *resp);
void ingestNewPackagesIntoQueue(int newCount, int currentTurn);
void syncTruckPositionsFromShared();

// ---- Assignment algorithm (simple version) ----
// each truck picks one nearest unassigned package (greedy)
void assignPackagesSimple(int currentTurn);

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

