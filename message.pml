typedef Message {
    int from;
    int to;
    int payload;
}

mtype:message = { appendEntryRequest, appendEntryResponse, requestVoteRequest, requestVoteResponse }

