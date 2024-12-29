# tlads

Verify some old or new concepts/models/algorithms/ideas of distributed/discrete systems using TLA+.

## Projects

 | Project                                         | Description                                                                |
 | ---                                             | ---                                                                        |
 | [paxos-eb0](paxos-eb0/)                         | A basic Paxos with excluded ballot 0 optimization                          |
 | [multi-paxos-eb0](multi-paxos-eb0/)             | A Multi-Paxos implementation composed by [paxos-eb0](paxos-eb0/) instances |
 | [percolator](percolator/)                       | The Google's distributed transaction algorithm built on Bigtable           |
 | [sequencer](sequencer/)                         | A distributed sequence generator                                           |
 | [simplified-fast-paxos](simplified-fast-paxos/) | A simplified Fast Paxos implementation                                     |
 | [isolation-models](isolation-models/)           | Transaction Isolation Models                                               |

## TODO

What's Next:

- [X] Github CI
- [ ] Separate model from specification
- [X] Modeling Transaction Isolation Levels
- [x] Add Liveness Invariants
- [ ] Distributed Transaction On Sql Databases
- [ ] HLC and Quorum Intersection

## Q & A

#### Why are the TLA+ files unicode-based?

In short, Unicode-based has better readability rather than plain ASCII.

In the plain ASCII, many other projects will generate a styled pdf with the
TLA+ files for readability, there are some disadvantages:
+ pdf files don't work well with git
+ (pdf)Latex dependency
+ more efforts to sync the TLA+ files and pdf files

#### How do I input the unicode symbols?

Please read: https://github.com/tlaplus/tlaplus-standard/tree/main/unicode
