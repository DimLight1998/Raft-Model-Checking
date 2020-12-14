#include "message.pml"

chan NetworkSent = [0] of { Message };
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
        ::  true -> write.payload = buffer[0];
                    NetworkSent ! write;
                    buffer[0] = buffer[1];
                    buffer[1] = buffer[2];
                    buffer[2] = buffer[3];
        od
    od
}

proctype TestSender() {
    int i;
    for (i : 1 .. 30) {
        printf("@tss TestSender sent %d\n", i);
        Message send;
        send.payload = i;
        NetworkRecv ! send;
    }
}

proctype TestReceiver() {
    Message recv;
    do
    ::  NetworkSent ? recv;
        printf("@trr TestReceiver received %d\n", recv.payload);
    od
}

init {
    run UnreliableNetwork();
    run TestSender();
    run TestReceiver();
}

