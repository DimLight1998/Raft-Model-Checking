#define NUM_SERVER  5
#define NUM_MAJOR   3

int relativeOrder[NUM_SERVER];

chan orderIncreaseRequests = [0] of { int }

int gmin;
int gmax;
ltl S { [] (gmin == 0 && gmax < 5) }

proctype observer() {
    do
    ::  d_step {
        int it;
        gmin = relativeOrder[0];
        gmax = relativeOrder[0];
        for (it : 0 .. NUM_SERVER - 1) {
            gmin = (relativeOrder[it] < gmin -> relativeOrder[it] : gmin);
            gmax = (relativeOrder[it] > gmax -> relativeOrder[it] : gmax);
        }
    }
    od
}

proctype orderIncreser() {
    int  serverID;
    int  it;
    do
    ::  d_step {
        orderIncreaseRequests ? serverID;
        int rank = relativeOrder[serverID];
        bool hasSameRank = false;
        for (it : 0 .. NUM_SERVER - 1) {
            if
            ::  it != serverID && relativeOrder[it] == rank -> hasSameRank = true;
            ::  else -> skip;
            fi
        }
        if
        ::  hasSameRank ->
            for (it : 0 .. NUM_SERVER - 1) {
                if
                ::  it != serverID && relativeOrder[it] > rank -> relativeOrder[it]++;
                ::  else -> skip;
                fi
            }
            relativeOrder[serverID]++;
        ::  !hasSameRank ->
            for (it : 0 .. NUM_SERVER - 1) {
                if
                ::  it != serverID && relativeOrder[it] > rank -> relativeOrder[it]--;
                ::  else -> skip;
                fi
            }
        fi
    }
    od
}

proctype test_orderIncreaseRequestor() {
    do
    ::  atomic {
            int serverID;
            select(serverID: 0 .. NUM_SERVER - 1);
            orderIncreaseRequests ! serverID;
        }
    od
}

init {
    int it;
    for (it : 0 .. NUM_SERVER - 1) {
        relativeOrder[it] = 0;
    }
    run test_orderIncreaseRequestor();
    run orderIncreser();
}

