# Baseline verification

The reference checkout is `anthropics/formal-math` at `11b6c7e3c927df2658f513b6b68ea7f8929c62c5`, the merge of PR 51. The VP–VNP package pins Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. All nine dependencies were checked out at the revisions in its manifest. The upstream working tree was clean before the checks. It contains no `AGENTS.md` or `CONTRIBUTING.md`. Its README describes the subproject as an unmaintained research artifact closed to contributions. [Pinned project](https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp) · [Checking instructions](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/README.md)

`Statement.Computes` counts arithmetic straight-line gates, including field constants and variables. The target polynomial may occur at any earlier slot. The main bound concerns equality of formal multivariable polynomials over a field of fixed characteristic, with an absolute constant and a characteristic-dependent threshold. The Hamiltonian cycle result permits every characteristic. The permanent bound has the additional hypothesis that the characteristic differs from two. The other results address approximation over Laurent series and algebraic polynomial families. `Statement.VNP` sums over Boolean witnesses in the coefficient field. [Statement definitions](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L23) · [Solution module](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Solution.lean)

## Upstream checks

GitHub's exact-commit `verify (vp-vnp)` job records success for both `lake build` (with no unfinished proofs outside the challenge file) and the Palomar comparator step. This main-branch run skipped the previous-project-build restore step. The comparator configuration lists five declarations: `Solution.mainTheorem`, `Solution.mainTheoremApprox`, `Solution.separation`, `Solution.separationClosure`, and `Solution.permanent_over_real`. The script requires a successful comparison with the challenge statements, independent nanoda replay, and only `propext`, `Quot.sound`, and `Classical.choice`. This is upstream's reported result. [Verification job](https://github.com/anthropics/formal-math/actions/runs/45272623486/job/138036167794) · [Configuration](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/comparator.json) · [Verification script](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/.github/scripts/comparator-check.sh)

## Local setup and reproduction

The isolated checkout is `/workspace/formal-math`. The local toolchain printed `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`. Its release archive matched its GitHub-reported SHA-256 `890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`. The cache endpoint built into the pinned release returned HTTP CONNECT 403 in this environment. Mathlib's official public frontend served objects under the same version-specific hashes. The initial targeted fetch decompressed all 1,655 outstanding archives for `Mathlib.Combinatorics.Nullstellensatz`, `Mathlib.RingTheory.MvPolynomial.Homogeneous`, `Mathlib.Algebra.CharP.Lemmas`, `Mathlib.Algebra.MvPolynomial.Expand`, and `Mathlib.Tactic.Ring`. The full project uses `import Mathlib`, requiring the complete cache. [Lean release](https://github.com/leanprover/lean4/releases/tag/v4.33.1)

```bash
cd /workspace/formal-math/vp-vnp
export PATH=/workspace/.boolean-transfer-tools/lean-4.33.1-linux/bin:$PATH
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4-master
export MATHLIB_CACHE_DIR=/workspace/.boolean-transfer-tools/mathlib-cache
export LEAN_NUM_THREADS=3
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
bash ../.github/scripts/comparator-check.sh
```

For reproduction on another machine, start with `git clone https://github.com/anthropics/formal-math` and `git checkout 11b6c7e3c927df2658f513b6b68ea7f8929c62c5`. Use the project toolchain through elan or substitute its binary directory in `PATH`. Use a writable directory for `MATHLIB_CACHE_DIR`. The first three commands after the environment setup need Lean and its pinned dependencies. Comparator also requires working installations of Go, Cargo, jq, and a Linux kernel with usable Landlock.

The local invocation of `bash ../.github/scripts/comparator-check.sh` exited before compilation with `error: cargo is required`. A separate read-only ABI check of the Landlock system call returned `ENOSYS` both inside the ordinary command sandbox and from the outer executor. This prevents the prescribed independent sandboxed comparator check on this machine. The upstream verification job covers this exact source revision.

The full cache fetch succeeded via the official public endpoint. All 8,690 pinned archives were present after decompression. A direct local recheck of `lake env lean Statement.lean` then exited successfully with no diagnostics. The default build uses the four targets `Statement`, `Challenge`, `Solution`, and `Paper`.

**Local baseline result, 24 November 2026 UTC.** `lake build` exited 0: `Build completed successfully (9032 jobs).` All five unfinished-proof warnings appeared in the upstream trusted `Challenge.lean` statement file. `lake env lean scripts/PrintAxioms.lean` then exited 0. Each of the five declarations listed above reported exactly `[propext, Classical.choice, Quot.sound]`. The upstream checkout remained clean. Only the local Landlock-based comparator stage described above lacks a local pass.
