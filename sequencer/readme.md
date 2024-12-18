# Sequencer

This is a distributed sequence generator on the assumption that all servers have a bounded clock skew.

Files:
+ [Sequencer.tla](./Sequencer.tla): the specification of the Sequencer
+ [MCSequencer.tla](./MCSequencer.tla): Model Checking for Sequencer

Features:
+ Linearizability
+ Cached sequences for better performance
