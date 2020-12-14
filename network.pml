#include "message.pml"
#define NUM_SERVER 5

chan NetworkSent[NUM_SERVER] = [0] of { Message };
chan NetworkRecv = [0] of { Message };

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

init {
    run UnreliableNetwork();
    run TestSender();
    int i;
    for (i : 0 .. NUM_SERVER - 1) {
        run TestReceiver(i);
    }
}

