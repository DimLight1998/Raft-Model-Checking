#include "message.pml"
#define NUM_SERVER  5
#define NUM_MAJOR   3

mtype:status = { leader, candidate, follower }

chan NetworkSent[NUM_SERVER] = [1] of { mtype:message, int, int, int, int, bool }
chan NetworkRecv             = [1] of { mtype:message, int, int, int, int, bool }

proctype UnreliableNetwork() {
    int buffer[4];
    Message read;
    Message write;
    do
    ::  NetworkRecv ? read;
        do
        ::  true -> break;
        ::  true -> buffer[0] = read.payload;
        ::  true -> buffer[1] = read.payload;
        ::  true -> buffer[2] = read.payload;
        ::  true -> buffer[3] = read.payload;
        od

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
        if
        ::  true -> skip; /* decrease timer */
        ::  true ->
            skip; /* TODO timeout */
        ::  NetworkSent[serverID] ? [appendEntryRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryRequest, msg_receiverID, msg_senderID, msg_term, _, _;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [requestVoteRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteRequest, msg_receiverID, msg_senderID, msg_term, msg_candidateID, _;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [appendEntryResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryResponse, msg_receiverID, msg_senderID, msg_term, _, msg_success;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [requestVoteResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteResponse, msg_receiverID, msg_senderID, msg_term, _, msg_voteGranted;
            skip; /* TODO */
        fi
    ::  status == candidate ->
        if
        ::  true -> skip; /* decrease timer */
        ::  true ->
            skip; /* TODO timeout */
        ::  NetworkSent[serverID] ? [appendEntryRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryRequest, msg_receiverID, msg_senderID, msg_term, _, _;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [requestVoteRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteRequest, msg_receiverID, msg_senderID, msg_term, msg_candidateID, _;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [appendEntryResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryResponse, msg_receiverID, msg_senderID, msg_term, _, msg_success;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [requestVoteResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteResponse, msg_receiverID, msg_senderID, msg_term, _, msg_voteGranted;
            skip; /* TODO */
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
                ::  it != serverID  -> NetworkRecv ! requestVoteRequest, it, serverID, serverID, false;
                ::  else            -> skip
                fi
            }
        ::  NetworkSent[serverID] ? [appendEntryRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryRequest, msg_receiverID, msg_senderID, msg_term, _, _;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [requestVoteRequest, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteRequest, msg_receiverID, msg_senderID, msg_term, msg_candidateID, _;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [appendEntryResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? appendEntryResponse, msg_receiverID, msg_senderID, msg_term, _, msg_success;
            skip; /* TODO */
        ::  NetworkSent[serverID] ? [requestVoteResponse, _, _, _, _, _] ->
            NetworkSent[serverID] ? requestVoteResponse, msg_receiverID, msg_senderID, msg_term, _, msg_voteGranted;
            skip; /* TODO */
        fi
    od
}

init {
    run UnreliableNetwork();
    run TestSender();
    int i;
    for (i : 0 .. NUM_SERVER - 1) {
        run TestReceiver(i);
    }
}

