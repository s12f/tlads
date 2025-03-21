# Spanner

[Spanner](https://static.googleusercontent.com/media/research.google.com/en//archive/spanner-osdi2012.pdf) is a Google's Globally-Distributed Database,
which inspired many modern distributed databases included [tikv](https://github.com/tikv/tikv), [CockroachDB](https://github.com/cockroachdb/cockroach) etc.
This project focuses on the [spanner-osdi2012](https://static.googleusercontent.com/media/research.google.com/en//archive/spanner-osdi2012.pdf) paper,
current Spanner probably has changed a lot.

- [x] [TrueTime.tla](./TrueTime.tla): TrueTime APIs
- [x] [DisjointLeases.tla](./DisjointLeases.tla): The implementation of Paxos leader election guarantees disjointness between leases.
- [x] [Transaction.tla](./Transaction.tla): The transaction implementation, included:
    - [x] Read-Write
    - [x] Read-Only
- [x] [TxTest.tla](./TxTest.tla): Models and Tests
- [x] Liveness Properties:
    - All transactions will eventually be committed or aborted.
    - All related locks will eventually be cleaned.
    - Note: verify liveness properties is more expensive (05min 19s with 8 workers) than safety, so the PROPERTIES in [TxTest.cfg](./TxTest.cfg) is commented by default.

More details: [Implement and Verify Google Spanner in TLA+](https://s12f.github.io/posts/2025-02-08-spanner-tlaplus.html)
