# Two pure matched ORs at 22 gates require at least three exceptional raws

The zero-, one-, and larger-shadow two-exception cases have already been excluded. The two-shadow placement analysis says a remaining case would have two repeated raws r and s at distinct split labels, two direct OR readers for each, and own-dirty ordinary mates on both labels. The six other ordinary split feeders have clean companions. This closes both remaining placements, whether r and s are on the same or opposite sides.

Choose an opposite ordinary raw t with label different from both r and s. There are at least three such split labels, and all ordinary on the chosen side. Zero r and t, then identify twins. The cut already removes five distinct OR gates: the two pure prefix ORs, the two OR readers of r (each aliases or becomes zero), and the sole OR feeder of t. The last gate cannot also read r, since that would mask t on r's diagonal, so all five losses are distinct.

The mate feeder of s is not one of these losses. Its retained raw and its own-dirty companion are both true on the original diagonal at s, where r=t=0, so it survives that elimination. On the tied cube its companion is true at the singleton for label s; by monotonicity OR-ing the companion with the raw twin adds nothing. Thus the mate feeder aliases, giving a sixth distinct OR loss. The projection is exact seven-variable threshold two, whose OR floor is ten. The original circuit therefore has at least sixteen ORs, hence at most six ANDs.

Erase the six ordinary feeders whose companions are clean. The terminal reconstruction needs at most five ORs for at most six productive ANDs; it preserves the two essential pure conduits. This gives a terminalized circuit of at most 21 gates, excluded by the two-pair terminalized bound, or forms more pure pairs, already excluded at size 22. Contradiction.

Thus an at-most-22 Crown7 candidate with exactly two pure matched ORs must have at least three exceptional split raws. The full question with three or more exceptions at two pairs, or with fewer pure pairs, is open. The argument is independent of finite solver results.
