[Percolator](https://www.usenix.org/legacy/event/osdi10/tech/full_papers/Peng.pdf)
is a distributed transaction algorithm built on Bigtable,
in the origin paper,
Percolator is designed for Large-scale Incremental Processing,
this project only specifies the core transaction part(without the notifications).

- Percolator.tla: Percolator Specification
- Transfer.tla: Verify the transfer transactions in the Percolator Specification.
- PhantomP3.tla: an example that Percolator allows Phantom P3 history(https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-95-51.pdf), so the tlc will fail, and outputs the state history.
