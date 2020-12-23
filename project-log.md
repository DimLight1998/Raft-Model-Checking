# Project Log

## Todolist

- [ ] 解决发包阻塞的问题（目前使用 `-m`）

## 2020-12-11

- 在进行了工具的比较之后我决定选择 SPIN 作为建模的语言，毕竟要 high-level 一些，写起来更加舒服。问题在于 SPIN 可能不是为这种类型的问题而设计的，不过它把消息传递设计为语言自带的特性这一点比较好。
- 学习 SPIN 中的基本概念。

## 2020-12-14

- 实现了一个不可靠的网络（把整数用作消息，用于示例）。
- 节点间的通信通过一个 `network` 进程实现。所有向 `network` 发送的包都使用一个专门的 channel，这些包中会指明希望发送到哪一个节点；`network` 通过这个信息再发往实际的节点。如果有 $n$ 个节点的话，总的 channel 数量应该是 $(n + 1)$。

## 2020-12-15

- 今天的目的是在不考虑宕机的情况下，实现领导者选举的验证。
- 为了建模服务器可以在任何时候崩溃，可以把是否工作做成一个 **全局** 的布尔变量，用一个进程来控制这个变量。
- 为什么需要把 channel 的 buffer 大小设置为 1？因为 *channel poll operations do not work on rendezvous channels because synchronous channels never store messages that a poll operation could refer to*，而我们需要 peek 一下第一个消息是什么类型。

### 消息的规范

| 消息类型            | 参数 (int)            | 参数 (int)          | 参数 (int)          | 参数 (int)             | 参数 (bool)          |
|---------------------|-----------------------|---------------------|---------------------|------------------------|----------------------|
| appendEntryRequest  | 消息接收者 receiverID | 消息发送者 senderID | 领导者任期 term     | （不使用）             | （不使用）           |
| requestVoteRequest  | 消息接收者 receiverID | 消息发送者 senderID | 候选者任期 term     | 候选者编号 candidateID | （不使用）           |
| appendEntryResponse | 消息接收者 receiverID | 消息发送者 senderID | 发送者任期猜测 term | （不使用）             | 接收心跳包 success   |
| requestVoteResponse | 消息接收者 receiverID | 消息发送者 senderID | 发送者任期猜测 term | （不使用）             | 进行投票 voteGranted |

## 2020-12-16

- 我感觉现在的实现顺序有些问题；应该先实现每种角色重叠的行为的，比如如果受到了任何消息，其中 term 要比自己的 currentTerm 大就更新自己的 currentTerm 这种。
- 发现了一个问题：现在的网络通信存在问题！发送了一个包之后应该马上返回，但是现在的实现中还是会阻塞（直到包进入缓存）。目前可以通过加上 `-m` 参数来暂时规避这个问题，不过这不是长久之计。

---

为什么会出现下面这种问题？明明只有一个 leader 产生，但是会有多个 server 从 leader 状态退出？

```shell
$ spin -m -T network.pml
server 0 changed to leader at term 3562
server 0 changed from leader to follower at term 3563
server 1 changed from leader to follower at term 3563
server 0 changed to leader at term 7746
server 0 changed from leader to follower at term 7747
server 0 changed to leader at term 24614
server 1 changed from leader to follower at term 24615
server 0 changed from leader to follower at term 24615
server 1 changed to leader at term 25212
server 1 changed from leader to follower at term 25213
server 1 changed to leader at term 27272
server 1 changed from leader to follower at term 27273
server 0 changed from leader to follower at term 27273
server 0 changed to leader at term 46825
server 0 changed from leader to follower at term 46826
server 0 changed to leader at term 50563
server 1 changed to leader at term 116908
server 1 changed from leader to follower at term 116909
server 0 changed from leader to follower at term 116909
server 0 changed to leader at term 122282
server 0 changed from leader to follower at term 122283
server 0 changed to leader at term 124938
server 0 changed from leader to follower at term 124939
server 1 changed to leader at term 129640
server 1 changed from leader to follower at term 129641
server 0 changed from leader to follower at term 129641
server 0 changed to leader at term 129784
server 0 changed from leader to follower at term 129785
server 1 changed from leader to follower at term 129785
```

---

### 消息的规范（更新）

| 消息类型            | 参数 (int)            | 参数 (int)          | 参数 (bool)             | 参数 (bool)          |
|---------------------|-----------------------|---------------------|-------------------------|----------------------|
| appendEntryRequest  | 消息接收者 receiverID | 消息发送者 senderID | 是否需要更新 needUpdate | （不使用）           |
| requestVoteRequest  | 消息接收者 receiverID | 消息发送者 senderID | 是否需要更新 needUpdate | （不使用）           |
| appendEntryResponse | 消息接收者 receiverID | 消息发送者 senderID | 是否需要更新 needUpdate | 接收心跳包 success   |
| requestVoteResponse | 消息接收者 receiverID | 消息发送者 senderID | 是否需要更新 needUpdate | 进行投票 voteGranted |


