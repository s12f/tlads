## Background

You probably need to read the [Lamport Paxos](https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf) paper
or other papers/docs about Basic Paxos first.

In classic Basic Paxos,
the core idea is that if there exists a quorum(Q1) of acceptors voted a value at a ballot(B1),
then for all the ballots greater than B1,
every quorum intersecting with Q1 will learn the value in phase 1,
which means the value is committed.

So the classic Basic Paxos always need two-round trip communication between a proposer and acceptors
to commit a value:

* Phase1: Learn the possible voted/committed value in a quorum of acceptors.
* Phase2: recover the voted value or issue a new value if not found any voted value.

But in practice, two-round trip to commit a value is quite expensive,
for an example, raft[https://raft.github.io/raft.pdf] or some other multi-paxos implements,
in normal case, committing a value only need one-round trip.

## Paxos with excluded ballot 0 optimization

If we set the ballots as a subset of Nat,
then ballot 0 is the bottom(minimum) ballot number,
so the proposal with ballot 0,
it doesn't need to learn any voted value(there will not exist any other ballots less than 0),
which means it can skip the Phase1,
and vote a new value to acceptors directly.

But it is safe if the ballot 0 is excluded by a proposer,
if there are multiple proposers use the ballot 0 to vote a different value directly,
then can't keep safety and liveness in normal classic Paxos Quorum(
[Fast Paxos](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-112.pdf)
is a solution for that).

So we can set the ballot 0 as the fast path(one-round trip),
other ballots as recover path(two-round trip).
Then based on this property,
you can compose the basic paxos instances to build you efficient Multi-Paxos implements,
[multi-paxos-eb0](../multi-paxos-eb0) is an example.
