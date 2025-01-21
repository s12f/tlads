# Spanner

[Spanner](https://static.googleusercontent.com/media/research.google.com/en//archive/spanner-osdi2012.pdf) is a Google's Globally-Distributed Database,
which inspired many modern distributed databases included [tikv](https://github.com/tikv/tikv), [CockroachDB](https://github.com/cockroachdb/cockroach) etc.
This project focuses on the [spanner-osdi2012](https://static.googleusercontent.com/media/research.google.com/en//archive/spanner-osdi2012.pdf) paper,
current Spanner probably has changed a lot.

- [x] [TrueTime.tla](./TrueTime.tla): TrueTime APIs
- [x] [DisjointLeases.tla](./DisjointLeases.tla): The implementation of Paxos leader election guarantees disjointness between leases.
- [ ] Transaction

