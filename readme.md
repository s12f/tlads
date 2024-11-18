# tlads: Tla+ and Distributed/Discrete Systems.

## Projects

| Project | Description |
| --- |  --- |
| [paxos-eb0](paxos-eb0/) | A Basic Paxos with excluded ballot 0 optimization |
| [multi-paxos-eb0](multi-paxos-eb0/) | A Multi-Paxos implement composed by paxos-eb0 instances |
| [percolator](percolator/) | the Google's Distributed Transaction Algorithm built on Bigtable |
| [sequencer](sequencer/) | A Distributed sequence generator |
| [simplified-fast-paxos](simplified-fast-paxos/) | a simplified fast paxos implement |

## TODO
- [ ] linearizable History
- [ ] Improve Sequencer: linearizable Point
- [ ] Multi-Paxos:
    - [ ] Batching
    - [ ] Log Completeness
- [ ] HLC and Quorum Intersection
- [ ] Distributed Transaction On Sql Databases
- [ ] Modeling Transaction Isolation Levels
