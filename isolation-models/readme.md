# Transaction Isolation Models

There are different isolation models to specify the database transaction isolation levels:

+ ANSI: ANSI/ISO SQL-92 and [A Critique of ANSI SQL Isolation Levels](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-95-51.pdf)
+ ADYA:
    + [Generalized Isolation Level Definitions](https://pmg.csail.mit.edu/papers/icde00.pdf)
    + [Weak Consistency: A Generalized Theory and Optimistic Implementations for Distributed Transactions](https://pmg.csail.mit.edu/papers/adya-phd.pdf)
+ SIB: [Seeing is Believing: A Client-Centric Specification of Database Isolation](https://www.cs.cornell.edu/lorenzo/papers/Crooks17Seeing.pdf)

Since SIB is the cleaner and easier to understand, implement and use to verify isolation levels of applications
(e.g. [percolator](../percolator), [spanner](../spanner)) compared with ANSI and ADYA,
so this project only implement the SIB model currently.

## SIB

[SIB_ISOLATION.tla](./SIB_ISOLATION.tla) is the specification of SIB isolation
model. You can use the IsolationExecution-related(e.g. SerializableExecution)
operations to verify a transaction execution(included an `init` state and a
transaction sequence). Or use the Isolation-related operations(e.g.
SerializableIsolation) to verify an `init` state and a set of finished
transaction(committed or abort). There is an example to verify that the
Snapshot Isolation allows the Write Skew anomaly, but the Serializable
Isolation Doesn't:
```tla
init ≜ [ k1 ↦ 0, k2 ↦ 0, k3 ↦ 0 ]

txs ≜
    { [ read ↦ [ k1 ↦ 0 ], write ↦ [ k2 ↦ 1 ] ]
    , [ read ↦ [ k2 ↦ 0 ], write ↦ [ k1 ↦ 1 ] ]
    }

SI ≜ INSTANCE SIB_ISOLATION

ASSUME SI!SnapshotIsolation(init, txs)
ASSUME ¬ SI!SerializableIsolation(init, txs)
```

More examples please see [SIB_TESTS.tla](./SIB_TESTS.tla).
