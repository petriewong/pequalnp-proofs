# Scoped case: 7 paired flags and exactly two singleton-accepting AND helpers

This is local research, not a solution to the full 22-gate crown challenge. The finite search is for a 15-gate logical threshold-two circuit after paying for the seven physical input pairings, with five ANDs, exactly two singleton-accepting AND helpers and three productive clean terms collected by a final two-gate OR tree. The eight remaining OR gates route unions of raw flags and helper outputs.

The search assumes the six-input 13-gate lower bound: zeroing a raw flag can collapse at most two gates, so there are at most two consuming gates per flag. In normal form a raw reader is always OR; a lone OR reader would mask the flag on a singleton accepted by its other operand (all routing wires accept some singleton). Consequently there are exactly fourteen direct raw-reader incidences, at least six raw-pair ORs and at most two more complex routing ORs. The search uses this bound and disjoint singleton support of each clean term. A distinct required union with a helper atom or more than two raw flags requires one non-raw-pair gate. Distinct clean terms cannot share an operand (factoring by distributivity would reduce the AND count without increasing size). No statement about arbitrary circuits of this size follows solely from this enumeration.

Replay (C++17 compiler):

```sh
c++ -std=c++17 -O3 -Wall -Wextra PairedFiveTwoReplay.cpp -o replay
for i in 0 1 2 3 4; do
  ./replay 8 "$i" 5
done
```

Each shard should print its `complete paired5 two dirty, budget 8 shard i/5` footer and no `FOUND` line. Expected enumerated helper counts: 51262, 52727, 38779, 29849, 25288. These counts are candidates visited before filters, not circuits classified individually. The checker models monotone behavior on all singletons and distinct pairs; those rows characterize threshold two for monotone circuits.
