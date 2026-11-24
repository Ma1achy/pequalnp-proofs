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
for module in CircuitDAG BooleanIdeal Frobenius MinTerm PartialLayer SquaringCost CircuitTransfer TourLayer SourceBridge; do
  printf 'Checking %s\n' "$module.lean"
  "$lean" -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
if [[ -n ${BOOLEAN_NANODA:-} || -n ${BOOLEAN_LEAN4EXPORT:-} ]]; then
  python3 audit_axioms.py "$companion" --lean4export "${BOOLEAN_LEAN4EXPORT:?}" --nanoda "${BOOLEAN_NANODA:?}"
else
  python3 audit_axioms.py "$companion"
fi
python3 boolean_jet.py
