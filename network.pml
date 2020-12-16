#include "message.pml"
#define NUM_SERVER  5
#define NUM_MAJOR   3

mtype:status = { leader, candidate, follower }

chan NetworkSent[NUM_SERVER] = [1] of { mtype:message, int, int, int, int, bool }
chan NetworkRecv             = [1] of { mtype:message, int, int, int, int, bool }

int  global_lastLeaderID = -1;
int  global_lastLeaderTerm = -1;
bool global_multiLeaderInOneTerm = false;
ltl  electionSafety { [] (!global_multiLeaderInOneTerm) }

proctype ReliableNetwork() {
    mtype:message messageHead;

    int  msg_f1;
    int  msg_f2;
    int  msg_f3;
    int  msg_f4;
    bool msg_f5;

    do
    ::  true ->
        NetworkRecv         ? messageHead, msg_f1, msg_f2, msg_f3, msg_f4, msg_f5;
        NetworkSent[msg_f1] ! messageHead, msg_f1, msg_f2, msg_f3, msg_f4, msg_f5;
    od
}

proctype UnreliableNetwork() {
    int buffer[4];
    Message read;
    Message write;
    do
    ::  true ->
        NetworkRecv ? read;
        if :: true -> skip; :: true -> buffer[0] = read.payload; fi
        if :: true -> skip; :: true -> buffer[1] = read.payload; fi
        if :: true -> skip; :: true -> buffer[2] = read.payload; fi
        if :: true -> skip; :: true -> buffer[3] = read.payload; fi
        do
        ::  true -> break;
        ::  true -> write.payload = read.payload;
                    write.from = read.from;
                    write.to = read.to;
                    NetworkSent[read.to] ! write;
                    buffer[0] = buffer[1];
                    buffer[1] = buffer[2];
                    buffer[2] = buffer[3];
        od
    od
}

proctype TestSender() {
    int i;
    for (i : 1 .. 30) {
        Message send;
        send.payload = i;
        send.from = 0;
        int sendTo = 0;
        do
        ::  sendTo < NUM_SERVER - 1 -> sendTo++;
        ::  sendTo > 0              -> sendTo--;
        ::  true                    -> break;
        od;
        send.to = sendTo;
        NetworkRecv ! send;
        printf("@tss TestSender sent %d to %d\n", i, sendTo);
    }
}

proctype TestReceiver(int serverNo) {
    Message recv;
    do
    ::  NetworkSent[serverNo] ? recv;
        printf("@trr%d TestReceiver received %d from server #%d\n", serverNo, recv.payload, recv.from);
    od
}

proctype Server(int serverID) {
    int currentTerm = 0;  /* latest term server has seen; initialized to 0 */
    int votedFor    = -1; /* candidateID that received vote in current term; -1 if none */

    mtype:status status    = follower; /* status of current server; initialized to follower */
    int votedForMe         = 0;        /* number of servers voted for this server when it is candidate */

    int it;

    int msg_receiverID;
    int msg_senderID;
    int msg_candidateID;
    int msg_term;
    bool msg_success;
    bool msg_voteGranted;

    do
    ::  status == leader ->
        printf("leader #%d, term %d, status: %d\n", serverID, currentTerm, status);
        /* update global leader information */
        if
        ::  global_lastLeaderTerm < currentTerm ->
            global_lastLeaderTerm = currentTerm;
            global_lastLeaderID = serverID;
        ::  global_lastLeaderTerm == currentTerm && global_lastLeaderID != serverID ->
            global_multiLeaderInOneTerm = true;
        fi
        if
        ::  true -> skip; /* decrease timer */
        ::  true ->
            for (it : 0 .. NUM_SERVER - 1) {
                if
                ::  it != serverID  -> NetworkRecv ! appendEntryRequest, it, serverID, currentTerm, 0, false;
                ::  else            -> skip
                fi
            }
        ::  NetworkSent[serverID] ? [appendEntryRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryRequest, msg_receiverID, msg_senderID, msg_term, _, _;
            if
            ::  msg_term < currentTerm ->
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, false;
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = -1;
                votedForMe = 0;
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, true;
            ::  msg_term == currentTerm ->
                skip /* such situation should not happen as there is atmost one leader */
            fi
        ::  NetworkSent[serverID] ? [requestVoteRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteRequest, msg_receiverID, msg_senderID, msg_term, msg_candidateID, _;
            if
            ::  msg_term < currentTerm ->
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, false;
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = msg_candidateID;
                votedForMe = 0;
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, true;
            ::  msg_term == currentTerm ->
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, false;
            fi
        ::  NetworkSent[serverID] ? [appendEntryResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryResponse, msg_receiverID, msg_senderID, msg_term, _, msg_success;
            if
            ::  msg_term < currentTerm ->
                skip /* it can do nothing */
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = -1;
                votedForMe = 0;
            ::  msg_term == currentTerm ->
                skip /* such case should not happen */
            fi
        ::  NetworkSent[serverID] ? [requestVoteResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteResponse, msg_receiverID, msg_senderID, msg_term, _, msg_voteGranted;
            if
            ::  msg_term < currentTerm ->
                skip /* it can do nothing */
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = -1;
                votedForMe = 0;
            ::  msg_term == currentTerm ->
                skip /* everything is normal (and success should be true) */
            fi
        fi
    ::  status == candidate ->
        if
        ::  true -> skip; /* decrease timer */
        ::  true ->
            currentTerm++;
            votedFor = serverID;
            votedForMe = 1;
            for (it : 0 .. NUM_SERVER - 1) {
                if
                ::  it != serverID  -> NetworkRecv ! requestVoteRequest, it, serverID, currentTerm, serverID, false;
                ::  else            -> skip
                fi
            }
        ::  NetworkSent[serverID] ? [appendEntryRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryRequest, msg_receiverID, msg_senderID, msg_term, _, _;
            if
            /* case: outdated sender server; send newer term by currentTerm; reject entry appending */
            ::  msg_term < currentTerm ->
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, false;
            /* case: current server is outdated; convert to follower */
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = -1;
                votedForMe = 0;
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, true;
            /* case: with in the same term, a leader has already be elected; convert to follower */
            ::  msg_term == currentTerm ->
                status = follower;
                votedFor = -1;
                votedForMe = 0;
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, true;
            fi
        ::  NetworkSent[serverID] ? [requestVoteRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteRequest, msg_receiverID, msg_senderID, msg_term, msg_candidateID, _;
            if
            ::  msg_term < currentTerm ->
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, false;
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = msg_candidateID;
                votedForMe = 0;
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, true;
            ::  msg_term == currentTerm ->
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, false;
            fi
        ::  NetworkSent[serverID] ? [appendEntryResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryResponse, msg_receiverID, msg_senderID, msg_term, _, msg_success;
            skip; /* ignored; candidate should not handle such response; it must be sent from an outdated server */
        ::  NetworkSent[serverID] ? [requestVoteResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteResponse, msg_receiverID, msg_senderID, msg_term, _, msg_voteGranted;
            if
            /* case: get a vote; check if we have the vote from the majority; change to leader if yes */
            ::  msg_term == currentTerm && msg_voteGranted == true ->
                votedForMe++;
                if
                ::  votedForMe >= NUM_MAJOR -> status = leader; printf("%d changed to leader at %d\n", serverID, currentTerm);
                ::  else -> skip;
                fi
            /* case: current server is outdated; convert to follower */
            ::  msg_term > currentTerm ->
                status = follower;
                currentTerm = msg_term;
                votedFor = -1;
                votedForMe = 0;
            /* case: maybe the server has already voted for someone else */
            ::  else -> skip;
            fi
        fi
    ::  status == follower ->
        if
        ::  true -> skip; /* decrease timer */
        ::  true ->
            status = candidate;
            currentTerm++;
            votedFor = serverID;
            votedForMe = 1;
            for (it : 0 .. NUM_SERVER - 1) {
                if
                ::  it != serverID  -> NetworkRecv ! requestVoteRequest, it, serverID, currentTerm, serverID, false;
                ::  else            -> skip
                fi
            }
        ::  NetworkSent[serverID] ? [appendEntryRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryRequest, msg_receiverID, msg_senderID, msg_term, _, _;
            if
            /* case: outdated sender server; send newer term by currentTerm; reject entry appending */
            ::  msg_term < currentTerm ->
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, false;
            /* case: this server is outdated; update currentTerm; accept entry appending */
            ::  msg_term > currentTerm ->
                currentTerm = msg_term;
                votedFor = -1;
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, true;
            /* case: this server and sender server is up-to-date; accept heartbeat */
            ::  msg_term == currentTerm ->
                NetworkRecv ! appendEntryResponse, msg_senderID, serverID, currentTerm, 0, true;
            fi
        ::  NetworkSent[serverID] ? [requestVoteRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteRequest, msg_receiverID, msg_senderID, msg_term, msg_candidateID, _;
            if
            /* case: outdated candidate; send newer term by currentTerm; reject vote */
            ::  msg_term < currentTerm ->
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, false;
            /* case: this server is outdated; update currentTerm; grant vote */
            ::  msg_term > currentTerm ->
                currentTerm = msg_term;
                votedFor = msg_candidateID;
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, true;
            /* case: this server and candidate is up-to-date; vote if not voted yet or voted for the same candidate */
            ::  msg_term == currentTerm && (votedFor == -1 || votedFor == msg_candidateID) ->
                votedFor = msg_candidateID;
                NetworkRecv ! requestVoteResponse, msg_senderID, serverID, currentTerm, 0, true;
            fi
        ::  NetworkSent[serverID] ? [appendEntryResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryResponse, msg_receiverID, msg_senderID, msg_term, _, msg_success;
            /* ignored; follower should not handle response; it must be sent from an outdated server */
        ::  NetworkSent[serverID] ? [requestVoteResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteResponse, msg_receiverID, msg_senderID, msg_term, _, msg_voteGranted;
            /* ignored; follower should not handle response; it must be sent from an outdated server */
        fi
    od
}

init {
    run ReliableNetwork();
    int i;
    for (i : 0 .. NUM_SERVER - 1) {
        run Server(i);
    }
}

