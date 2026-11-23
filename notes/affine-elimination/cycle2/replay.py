"""Replay the second-cycle experiments and compare their four saved results."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parent


def run(command):
    return subprocess.run(command, cwd=ROOT, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                          check=True, text=True, stdout=subprocess.PIPE).stdout


def check_equal(actual, expected, label):
    if actual != expected:
        raise ValueError(f"replay differed from {label}")
    print(f"Matched {label}", flush=True)


def saved_json(name):
    return json.loads((ROOT / name).read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"), help="Lean 4.36.0 executable")
    parser.add_argument("--solver", help="include the recorded CaDiCaL 2.1.2 probe")
    args = parser.parse_args()
    if not args.lean or "4.36.0" not in run([args.lean, "--version"]):
        parser.error("use Lean 4.36.0 on PATH or pass --lean PATH")
    run([args.lean, "InterfaceCover.lean"])
    print("Checked InterfaceCover.lean", flush=True)

    python = sys.executable
    for name in ("five_points", "geometric", "generator_flat", "matching_encoding",
                 "tour_encoding", "assignment_lower", "order_search", "weighted_checks",
                 "weighted_profile", "weighted_slices", "weighted_syndrome"):
        run([python, name + ".py"])
        print(f"Passed {name}.py", flush=True)
    check_equal(run([python, "constructions.py"]), (ROOT / "constructions-results.txt").read_text(),
                "constructions-results.txt")
    check_equal(json.loads(run([python, "mixed_line.py"])), saved_json("mixed_line.json"),
                "mixed_line.json")
    with TemporaryDirectory() as temp:
        output = Path(temp) / "results.json"
        run([python, "synthesis_points.py", "--output", output])
        check_equal(json.loads(output.read_text()), saved_json("synthesis-points-results.json"),
                    "synthesis-points-results.json")
        command = [python, "synthesis.py", "--output", output]
        expected = saved_json("synthesis-results.json")
        if args.solver:
            if run([args.solver, "--version"]).strip() != expected["solver_version"]:
                parser.error("the saved optional solver probe uses CaDiCaL 2.1.2")
            command.extend(["--probe", "--solver", args.solver])
        else:
            expected.pop("probes")
            expected.pop("solver_version")
            print("Optional CaDiCaL probe omitted", flush=True)
        run(command)
        check_equal(json.loads(output.read_text()), expected, "synthesis-results.json")


if __name__ == "__main__":
    main()
