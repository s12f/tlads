## Background

you should read [paxos-eb0](../paxos-eb0) first.

## Motivation

multi-paxos-eb0 is a Multi-Paxos implementation composed by paxos-eb0 instances,
for every paxos-eb0 instance,
we always need an excluded proposer(leader) to commit a value in the fast path,
multi-paxos-eb0 is not a stable/strong leader-based implementation,
the Leader role only means it can vote directly in the next sequence.

So a typical multi-paxos-eb0 history is:

1. A Proposer(P1) proposes and commits a request(using slow path), then the proposer sets itself as a Leader
2. Clients learn P1 as the Leader, then send requests to P1
3. P1 continues to vote and commit income requests using the fast path
4. If P1 crashed or network partitioned, the clients or Load Balancer will send requests to other proposers.
5. Back to step 1.

In the worst case, a network partition happened,
and two proposers both think they are the Leader,
that doesn't affect safety, and the system will be still available,
but due to the conflicts,
the performance will slow down compared with the normal case.

Compare with [raft](https://raft.github.io/raft.pdf),
multi-paxos-eb0 has higher availability,
but without a steady/strong leader,
so you can't guarantee the linearizable read from a single leader node,
typical raft implementation use lease read(read on leader is linearizable, but requires time synchronization).

So multi-paxos-eb0 is probably useful in distributed log/message storage systems(higher availability and read is typically sequential)
or other systems that require higher availability but not frequent linearizable read.

## Checking time

   | Hardware | Ballot | Seq       | time       |
   | ---      | ---    | ---       | ---        |
   | 8 Cores  | {0, 1} | {0, 1}    | 1s         |
   | 8 Cores  | {0, 1} | {0, 1, 2} | 13 min 21s |

## TODO

- [ ] Batching
- [ ] Log Completeness
