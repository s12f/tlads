# Transaction Isolation Models

There are different isolation models to specify the database transaction isolation levels:

+ ANSI: ANSI/ISO SQL-92 and [A Critique of ANSI SQL Isolation Levels](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-95-51.pdf)
+ ADYA:
    + [Generalized Isolation Level Definitions](https://pmg.csail.mit.edu/papers/icde00.pdf)
    + [Weak Consistency: A Generalized Theory and Optimistic Implementations for Distributed Transactions](https://pmg.csail.mit.edu/papers/adya-phd.pdf)
+ SIB: [Seeing is Believing: A Client-Centric Specification of Database Isolation](https://www.cs.cornell.edu/lorenzo/papers/Crooks17Seeing.pdf)

## SIB

[SIB_ISOLATION.tla](./SIB_ISOLATION.tla) is the specification of SIB isolation
model, you can use the IsolationExecution-related(e.g. SerializableExecution)
operations to verify a transaction execution(included an init state and a
transaction sequence), or use the Isolation-related operations(e.g.
SerializableIsolation) to verify an init state and a set of finished
transaction(committed or abort), there is an example to verify that the
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

### TODO

- Parallel Snapshot Isolation
- Read Atomic

## ANSI

TODO.

## ADYA

TODO.
