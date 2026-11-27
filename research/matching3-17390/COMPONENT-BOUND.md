# Even with NOT, 3×3 perfect matching needs 14 gates

This is a structural proof with two small, exhaustively checked truth-table facts. All nine raw inputs are essential. The 14-gate AND/OR formula in PerfectMatching14.lean gives a matching upper bound.

## 1. Split any circuit into formula components

Take a live circuit, normalize constant gates, repeated operands, and harmless unary AND/OR gates, so each AND/OR has two incoming wires and NOT has one. Call an input or internal gate **shared** if it has at least two consumers. Let r be the number of shared raw inputs and h the number of shared internal gates.

Cut the outgoing connections of each shared internal gate, treating its signal as a named input in later components. The roots of the resulting formula components are the h shared internal gates in a topological order, followed by the final output. Every nonshared gate belongs to a unique such formula: follow its unique downstream consumer until the first component root. Every nonshared raw input is used exactly once and belongs to one component. The repeated raw inputs may appear in any component; they will be fixed when needed.

## 2. The nonshared raw inputs in one component are all in one row or column

If two nonshared raw inputs x,y are in one component, neither can affect the rest of the circuit except through that component's one root bit. With all other raw inputs fixed, every earlier component signal is constant with respect to x,y, and the remaining circuit is a unary Boolean map of the current component's result. In its formula, x and y each occur once. Push NOT gates to the literals. Their signs and their least common ancestor's operation are now fixed by syntax. With other inputs set to constants, a restriction depending on both x and y uses that same operation on the two signed literals. The downstream unary map, if nonconstant, is identity or negation. For the final two-variable restriction to be monotone and depend on both variables, the literal signs must agree, and the unary map then has only one possible sign. Therefore no two contexts can give AND in one and OR in the other.

The first truth-table fact is that every pair of edges in different rows and different columns has both restrictions in the matching function (18 pairs, two witnesses per pair). Consequently, within a component, each pair of nonshared edges has a common row or column. Any such edge set is contained in one row or one column and has size at most three: for two edges in the same row with different columns, another edge outside that row could not share both columns, and the column argument is symmetric.

## 3. In fact there must be at least six shared nodes

The second truth-table fact: for any adjacent edge pair x,y (sharing a row or column) and any specified set Z of five distinct other edges, there is a setting of Z such that the four settings of x,y generate at least three distinct functions on the two remaining free edges. The same conclusion holds when Z has fewer than five edges, by extending Z first and then noting that distinctions on the smaller domain persist on the larger domain. This fact is certified for 18 × 21 = 378 choices.

Suppose h+r≤5. Induct over the shared-root components in their topological order. Assume each earlier one has at most one nonshared raw input. If the current component contains two such inputs x,y, they are adjacent by step 2. Fix all r shared raw inputs, all earlier nonshared component inputs (at most h−1), and the current component's possible third nonshared raw input (at most one). This specifies a set of at most r+h≤5 edges, excluding x,y. Fix them according to the second truth-table fact. The earlier component outputs now are constant, and the current root is a Boolean function of x,y alone. Every outside dependence on x,y goes through that one bit, so there can be at most two distinct cofactors of the whole circuit as x,y vary. This contradicts the three certified distinct cofactors.

Each shared-root component therefore contains at most one nonshared raw input, and the output component has at most three by step 2. Counting all nine raw inputs gives 9−r≤h+3, hence h+r≥6, a contradiction. Thus every such circuit has at least six shared nodes.

## 4. Convert sharing to a gate count

If a normalized circuit has k gates of which t are unary NOT, the number of operand edges is 2k−t. There are 9+k−1 nonoutput vertices, all of which are live and have at least one consumer. The six shared vertices each contribute at least one more edge, so 2k−t≥(9+k−1)+6, or k≥14+t. In particular no counted-NOT circuit uses 13 or fewer gates, and if a normalized circuit actually uses a NOT it needs at least 15 gates. The 14-gate witness is optimal whether NOT is permitted or not.

## Reproduce the finite facts

Run python3 component_witnesses.py. It exhaustively validates both facts and writes MatchingComponentChecks.lean. Compiling that file checks the counts, coverage and individual witness inequalities in Lean, using the six permutation terms for the Boolean target. MatchingComponentPrinciples.lean separately checks the finite literal-sign and arithmetic ingredients. The circuit-to-component argument above is a paper proof, not an end-to-end theorem about Lean's circuit datatype. This negative result is not the affirmative construction requested by the associated upstream desk targets.
