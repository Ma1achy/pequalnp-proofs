# L-meta-2541

Ma1achy’s ordinary-input proof is on [collab/L-meta-2541-ordinary](https://github.com/Ma1achy/pequalnp-proofs/tree/collab/L-meta-2541-ordinary). The parent splits on whether input 0 is complemented. [Merged split](https://github.com/brilliant-hq/pequalnp-proofs/pull/4698)

For the flipped case, assume a circuit computes the Petersen-minus-one-vertex edge function, reads raw wire 0 in at most one gate, and has at most 14 gates. The ordinary lower bound then forces that gate to be a binary AND or OR of raw wire 0 and a valid earlier gate output. Whenever toggling 0 changes the target, the side operand is true for AND and false for OR. If the side operand is wire 9, the reader is OR and wire 9 computes an AND on the endpoints of an edge among vertices 1 through 8. The public theorem takes the exact ordinary child as its premise. [Lean proof](../lean/PEqualNP/Outside/SignedReader.lean)

For a subsequent first-gate lower bound, any gate that reads only raw inputs can be moved to the beginning of the list. The transformation preserves size and the circuit function, including when the original list has out-of-range or forward references. Input relabeling is available in the same module. [Gate movement proof](../lean/PEqualNP/Search/PetersenHoist.lean)

The open obligation is to exclude the remaining flipped circuits. The exact parent requires both input polarities.
