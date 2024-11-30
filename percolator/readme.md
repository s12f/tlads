[Percolator](https://www.usenix.org/legacy/event/osdi10/tech/full_papers/Peng.pdf)
is a distributed transaction algorithm built on Bigtable,
in the origin paper,
Percolator is designed for Large-scale Incremental Processing,
this project only specifies the core transaction part(without the notifications).

- Percolator.tla: Percolator Specification
- Transfer.tla: Verify the transfer transactions in the Percolator Specification.
- SnapshotRead.tla: Verify SnapshotRead.
