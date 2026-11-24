# Circuit bounds for two Petersen graph jobs

The desk assigned Ma1achy two counterexample searches on the same nine-input Boolean function. The function is true when the selected vertices contain both endpoints of an edge of the Petersen graph with one vertex deleted. Both jobs prescribe the first wire $x_0 \lor x_4$. L-meta-2150 requires an AND as the second gate, and L-meta-2152 requires an OR. Each asks for a circuit with at most 15 gates, permits sharing intermediate results, and counts every NOT gate. [L-meta-2150](https://pequalnp.com/lemma#L-meta-2150) · [L-meta-2152](https://pequalnp.com/lemma#L-meta-2152)

| Second gate | Verified circuit size | Gates above the requested limit |
| --- | ---: | ---: |
| AND | 18 | 3 |
| OR | 17 | 2 |

The certificates use the project's circuit evaluator and prove equality to the posted Boolean expression for every input. They also certify the position and operation of the second gate and that every gate input refers to an earlier wire. Both circuits pay for the prescribed first gate and leave its result unused. [Circuit witnesses](../lean/PEqualNP/Search/PetersenGateWitness.lean)

## Counting edge covers

The graph has 12 edges and minimum vertex cover size five. The outer five-cycle requires three vertices. The disjoint edges {5, 7} and {6, 8} require another two. The set {0, 2, 3, 5, 6} attains the bound.

Consider a formula that ORs together unshared terms of the form $(\bigvee A)\land(\bigvee B)$, where both parts of each term are nonempty sets of inputs. Each pair across a term must be an edge. Two distinct vertices have at most one common neighbor, so at least one part of each term is a singleton. The resulting star centers cover all edges, which requires at least five centers. A star with $d$ leaves costs $d$ gates, and combining $k$ stars costs another $k-1$. Covering all 12 edges therefore costs at least $12+5-1=16$ gates. Five explicit stars attain 16. Inputs 0 and 4 have no common neighbor, so their prescribed OR cannot feed the leaf disjunction of a sound star directly. [Cover and cost proofs](../lean/PEqualNP/Search/PetersenCoverBound.lean)

## A necessary condition for shared circuits

Every circuit with the prescribed first wire and the correct output must read raw input 0 again at some later gate. It must also read raw input 4 again. One gate may serve both purposes. To see the first requirement, fix input 4 to true and the other seven inputs to false. Toggling input 0 changes the target because {0, 4} is an edge, while the first wire stays true. Unless some later gate reads 0, the two assignments agree on every other wire. The symmetric pair proves the requirement for input 4. The formal proof also rules out selecting a raw input as the circuit output. This condition applies to circuits of every size, including those with shared gates and negations. [Necessary-reads proof](../lean/PEqualNP/Search/PetersenNecessaryReads.lean)

The same proof works for either AND or OR on any two distinct raw inputs of this graph. If a first wire depends on a single input instead, every other input must be read after it. [General pair and unary results](../lean/PEqualNP/Search/PetersenNecessaryReads.lean)

## Exact size when only the first two gates may be shared

A separate exhaustive C++ computation allows the two prescribed gates to feed any number of later gates. All later gates in the output circuit use AND or OR and have at most one consumer. The program computes the minimum formula size for that suffix. It identifies the 12 minimal true inputs and 12 maximal false inputs, then checks every possible signal for the second gate, including constant signals, repeats and out-of-range reads.

For a fixed choice of signals available to the suffix, a single leaf suffices if it separates the remaining true and false examples. An OR at the root partitions the true examples between two smaller formulas, and an AND partitions the false examples. Minimizing over these partitions gives the least number of leaves. Monotonicity extends correctness on the boundary to all 512 inputs. Of the 53 second-OR signals, 21 permit a 16-leaf suffix. All 55 second-AND signals require 17 leaves. Adding the two prescribed gates and charging one gate per internal formula node gives exact minima of 17 and 18 gates, respectively. The Lean witnesses above attain both values. The lower bounds in this paragraph come from the C++ computation. [Search implementation](../tools/petersen_formula_bound.cpp)

```sh
c++ -std=c++20 -O3 tools/petersen_formula_bound.cpp -o /tmp/petersen-formula
/tmp/petersen-formula
```

## Finite search for the posted statements

The project's evaluator allows arbitrary natural numbers as wire indices. At gate $j$, all indices at least $9+j$ read false. They can therefore be replaced by the single index $9+j$. The same argument caps the output index at nine plus the circuit size. Lean proves this normalization preserves wire values, gate positions, every opcode, fan-in, the output function and the gate count. For each posted statement, existence of a counterexample is equivalent to existence of one in this finite range. The 15-gate SAT searches did not exhaust the range. [Normalization and equivalence](../lean/PEqualNP/Search/PetersenWireBound.lean)

The connection to the binary pigeonhole work is methodological. Counting which objects a restricted proof or circuit can cover supplies a lower bound for that class. A pair of inputs that agree on the available information can rule out additional candidates. The pigeonhole theorem itself concerns a different proof system. The unrestricted 15-gate question for each second operation remains open in this work. [L-alg-006 research](https://github.com/Ma1achy/pequalnp-proofs/pull/1)
