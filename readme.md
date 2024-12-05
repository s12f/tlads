# tlads

Verify some old or new concepts/models/algorithms/ideas of distributed/discrete systems using TLA+.

## Projects

| Project                                         | Description                                                           |
| ---                                             | ---                                                                   |
| [paxos-eb0](paxos-eb0/)                         | A basic Paxos with excluded ballot 0 optimization                     |
| [multi-paxos-eb0](multi-paxos-eb0/)             | A Multi-Paxos implement composed by [paxos-eb0](paxos-eb0/) instances |
| [percolator](percolator/)                       | The Google's distributed transaction algorithm built on Bigtable      |
| [sequencer](sequencer/)                         | A distributed sequence generator                                      |
| [simplified-fast-paxos](simplified-fast-paxos/) | A simplified Fast Paxos implement                                     |

## TODO

What's Next:

- [x] Github CI
- [ ] Separate model from specification
- [ ] Modeling Transaction Isolation Levels
- [ ] Add Liveness Invariants
- [ ] Distributed Transaction On Sql Databases
- [ ] HLC and Quorum Intersection
