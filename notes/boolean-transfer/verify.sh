#!/usr/bin/env bash
# Run from any directory. Supply the vp-vnp subdirectory of the pinned checkout.
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo 'Usage: bash verify.sh /path/to/formal-math/vp-vnp' >&2
  exit 2
fi
companion=$(cd "$(dirname "$0")" && pwd)
upstream=$(cd "$1" && pwd)
revision=11b6c7e3c927df2658f513b6b68ea7f8929c62c5
if [[ $(git -C "$upstream" rev-parse HEAD) != "$revision" ]]; then
  echo "Expected the formal-math checkout at $revision" >&2
  exit 1
fi
cd "$upstream"
lake build Statement Paper.Flat Nc.Acc.Prog
project_path=$(lake env printenv LEAN_PATH)
lean=$(lake env which lean)
export PATH="$(dirname "$lean"):$PATH"
"$lean" --version
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build:$project_path"
cd "$companion"
for module in CircuitDAG BooleanIdeal Frobenius MinTerm PartialLayer SquaringCost CircuitTransfer TourLayer SourceBridge SparseRepeat EasyTourLayer CoverCost BallAgreement SurplusKernel ForcedTourWeight CircuitProjection LayerProjection SplicedTours SplicePermutation CoreCoefficient OrbitPadding ExactTourPadding TreewidthTransfer ArcWindow ArcRestrictions WindowCoefficients OracleTransfer ParseGuard UniquePromise PromiseIdeal; do
  printf 'Checking %s\n' "$module.lean"
  "$lean" -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
if [[ -n ${BOOLEAN_NANODA:-} || -n ${BOOLEAN_LEAN4EXPORT:-} ]]; then
  python3 audit_axioms.py "$companion" --lean4export "${BOOLEAN_LEAN4EXPORT:?}" --nanoda "${BOOLEAN_NANODA:?}"
else
  python3 audit_axioms.py "$companion"
fi
python3 boolean_jet.py
python3 sparse_repeats.py
python3 degree_checks.py
python3 sparse_tour.py
python3 surplus_kernel.py
python3 check_layer_projection.py
python3 check_orbit_padding.py
python3 anf_cores.py
python3 exact_tour_padding.py
python3 boolean_treewidth.py
python3 arc_window_search.py
python3 oracle_transfer.py
python3 guarded_parses.py
python3 affine_transcripts.py
python3 unique_tour_windows.py
python3 promise_isolation.py
python3 unique_verifier_gates.py
python3 unique_tour_gadget.py
