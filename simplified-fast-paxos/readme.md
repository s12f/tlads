## Background

You should read the [Fast Paxos](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-112.pdf) paper first.

## Motivation

Fast Paxos(and [Generalized Paxos](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-33.pdf))
is a very important paper(s) that inspires many future leaderless(multi-leader) paxos implements.

This project simplifies the origin Fast Paxos to make it more easily and practically to implement:

1. Remove the Empty value
2. Clients can't issue value to acceptors directly
3. Clients always send requests to proposers
4. Ballot 0 is the only fast round, all other ballots are classic round

In the Fast Paxos,
the fast round requires a bigger quorum than the classic round,
so in real practical systems,
if the fast round failed, it means there are some bad things happened
(e.g. conflicted values, crashed node, partitioned network etc.),
so it should always fall back to the classic round(requires smaller quorum) to recover,
that is why we only set ballot 0 as the fast round.

## Checking time
Hardware:

8Cores

Ballot = {0, 1},  => 06s
