# Project Log

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

