# Reducing the Heawood circuit search at the output gate

The site assigned Ma1achy L-meta-582. It asks whether 26 binary AND and OR gates can compute the edge function of the 14-vertex Heawood graph. Seven stars, one for each point of the Fano plane, give a 27-gate circuit. The 21 distinct edges are the minimal true inputs. The graph has 37 maximal independent sets, which are the maximal false inputs. Testing a monotone circuit on these 58 inputs suffices to establish its value on all 16,384. The boundary test also appears in an earlier proposed reduction. [Posted job](https://pequalnp.com/lemma#L-meta-582) · [Earlier boundary reduction](https://github.com/brilliant-hq/pequalnp-proofs/pull/3990)

## The three statements in the reduction

1. Find a monotone circuit with at most 25 gates and two internal wires. On the 58 boundary inputs, their OR or AND must equal the target. On a designated pair of inputs, the two wires must take opposite values and exchange values from one input to the other. The search allows three representative input pairs for a final OR and thirteen for a final AND. This circuit search remains open.
2. Appending one binary gate to the prefix produces an ordinary circuit whose output is the chosen AND or OR of those two wires. The gate increases the size by one. [Lean proof](../lean/PEqualNP/Search/HeawoodFinalGate.lean)
3. A monotone circuit that accepts the minimal true inputs and rejects the maximal false inputs is correct everywhere. The proof uses the pointwise order on Boolean assignments and works for any finite input width. [Lean proof](../lean/PEqualNP/Search/HeawoodBoundary.lean)

The one-file reduction proves that these three statements imply the exact desk goal. The local project checker accepted it and printed three children. The two linked proofs also typechecked against the exact second and third child types printed by that checker. [One-file reduction](https://github.com/Ma1achy/pequalnp-proofs/blob/8f357bb0dad287a9b6d3bbd27b12d81e2ad98eae/lean/PEqualNP/Outside/R_meta_582_317.lean)

## Why the search focuses on these pairs

Consider a smallest circuit for the target. Its last gate can be taken as the output. If the last gate is OR, both of its operands reject every negative input. Each operand must miss some positive input, since otherwise that operand alone would compute the target. Monotonicity lets us choose a minimal positive input it misses. The other operand must accept there. Doing this for both operands gives two distinct edges on which their values switch.

If the last gate is AND, both operands accept every positive input. Each must accept some negative input, since otherwise it alone would compute the target. Extend each such input to a maximal independent set. Monotonicity preserves acceptance by that operand, while the other operand must reject. Both operands of the last gate must be internal wires. For OR, a raw operand would accept its singleton. For AND, a raw operand would reject an edge avoiding that vertex.

The separate Python enumeration constructs all 336 graph automorphisms and allows the pair to be exchanged. It supplies a concrete permutation for each of the 210 unordered pairs of distinct edges and each of the 666 unordered pairs of distinct maximal independent sets. This gives the 3 and 13 representatives encoded in the reduction. The coverage calculation is independently executable. The Lean reduction proves sufficiency directly for the listed representatives. [Orbit generator](../tools/heawood_final_orbits.py)

```sh
python3 tools/heawood_final_orbits.py
python3 tools/heawood_final_orbits.py --certificate > /tmp/heawood-orbits.json
```

## An additional constraint on the remaining search

Lean also proves that any 26-gate witness must have some raw input read by exactly one gate among those that affect the output. The other operand of that gate must be a wire from an earlier gate. For an AND reader, that earlier wire must accept all three neighboring singleton assignments. For an OR reader, it must reject the other thirteen singleton assignments and all sixty independent pairs among those vertices. These conditions apply to circuits that share intermediate results. [Necessary input reads](../lean/PEqualNP/Search/HeawoodNecessaryReads.lean)
