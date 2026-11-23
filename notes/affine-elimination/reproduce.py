"""Run the independent experiment suites and replay the recorded traces."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent


def run(args, capture=False):
    return subprocess.run(args, cwd=ROOT, check=True, text=True,
                          stdout=subprocess.PIPE if capture else None).stdout


def equal_trace(actual, name):
    saved = (ROOT / name).read_text()
    if json.loads(actual) != json.loads(saved):
        raise ValueError(f"regenerated data differ: {name}")
    print(f"Verified {name}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="path to the pinned Lean 4.36.0 binary")
    args = parser.parse_args()
    lean = args.lean or shutil.which("lean")
    if not lean:
        parser.error("Lean 4.36.0 is needed for the two proof files; provide --lean")
    version = run([lean, "--version"], True).strip()
    print(version, flush=True)
    if "version 4.36.0," not in version and "version 4.36.0 " not in version:
        parser.error("reproduction uses the project's pinned Lean 4.36.0")
    for source in ("Projection.lean", "HelperCover.lean"):
        run([lean, source])
        print(f"Checked {source}", flush=True)
    python = sys.executable
    for args in (["formula_sat.py", "--check"], ["helper_blocks.py"], ["rank_certificates.py"],
                 ["verify_inner_product.py"], ["rigidity_checks.py"]):
        run([python, *args])
    with TemporaryDirectory() as tmp:
        for script, filename in (("experiments.py", "experiments.json"),
                                 ("quadratic_experiment.py", "quadratic-results.json")):
            output = Path(tmp) / filename
            run([python, script, "--output", output], True)
            equal_trace(output.read_text(), filename)
    equal_trace(run([python, "syndrome_checks.py"], True), "syndrome-results.json")
    equal_trace(run([python, "verify_inner_product.py", "--mux-trace"], True), "mux-results.json")
    print("All checks passed.", flush=True)


if __name__ == "__main__":
    main()
