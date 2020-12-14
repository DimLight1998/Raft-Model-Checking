chan NetworkSent = [0] of {int};
chan NetworkRecv = [0] of {int};

proctype UnreliableNetwork() {
    int buffer[4];
    int read;
    do
    ::  NetworkRecv ? read;
        do
        ::  true -> break;
        ::  true -> buffer[0] = read;
        ::  true -> buffer[1] = read;
        ::  true -> buffer[2] = read;
        ::  true -> buffer[3] = read;
        od

        do
        ::  true -> break;
        ::  true -> NetworkSent ! buffer[0];
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
        NetworkRecv ! i;
    }
}

proctype TestReceiver() {
    int recv;
    do
    ::  NetworkSent ? recv;
        printf("@trr TestReceiver received %d\n", recv);
    od
}

init {
    run UnreliableNetwork();
    run TestSender();
    run TestReceiver();
}

