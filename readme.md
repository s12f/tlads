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
| [spanner](spanner/)                             | Google’s Globally-Distributed Database                                     |
| [cache](cache/)                                 | Implement and verify the write-through caching strategy                    |

## Q & A

#### Why are the TLA+ files Unicode-based?

In short, Unicode-based has better readability rather than plain ASCII.

In the plain ASCII, many other projects will generate a styled PDF with the
TLA+ files for readability, there are some disadvantages:
+ PDF files don't work well with git
+ (PDF)Latex dependency
+ More efforts to sync the TLA+ files and PDF files

#### How do I input the Unicode symbols?

Please read: https://github.com/tlaplus/rfcs/tree/2a772d9dd11acec5d7dedf30abfab91a49de48b8/accepted_rfcs/rfc5_unicode
