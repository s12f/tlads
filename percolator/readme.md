[Percolator](https://www.usenix.org/legacy/event/osdi10/tech/full_papers/Peng.pdf)
is a distributed transaction algorithm built on Bigtable,
in the origin paper,
Percolator is designed for Large-scale Incremental Processing,
this project only specifies the core transaction part(without the notifications).

- [Percolator.tla](./Percolator.tla): Percolator Specification
- [Transfer.tla](./Transfer.tla): Verify the transfer transactions in the Percolator Specification.
- [SnapshotRead.tla](./SnapshotRead.tla): Verify SnapshotRead.
- [MC_SIB_SNAPSHOT.tla](./MC_SIB_SNAPSHOT.tla): Verify that percolator actually implemented the snapshot isolation.
    - TODO: improve the model checking for more possibility of the transactions.
