# Four-by-four one-hot table 15,14,5,3

The project Circuit in Table26013.lean evaluates a complement-on-the-promise circuit. The missing entries are row 1 col 0, row 2 col 1 or 3, and row 3 col 2 or 3. Their indicator uses seven AND/OR gates (two local OR, three AND, two final OR); one NOT negates the indicator. This evaluates exactly the given table when there is one row and one column on. Claiming agreement on arbitrary eight-bit patterns would be incorrect; the proof is for the declared one-hot promise. The file tests gate count, NOT count, order and fan-in on the actual upstream data type.

Local study pending official eligibility. The live desk showed L-meta-26013 leased by someone else, and we do not have its stashed exact Lean statement or an approved upstream lease. This file has not gone through the upstream checker and is not an upstream contribution.
