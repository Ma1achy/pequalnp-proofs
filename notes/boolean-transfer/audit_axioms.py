#!/usr/bin/env python3
"""Audit all public theorem roots in the companion's flat Lean source modules."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory


ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
NAME = r"[\w'.]+"
HEADER = re.compile(
    rf"^(?:@\[[^\n]*?\]\s*)*(?:(?:public|protected)\s+)*"
    rf"(?:lemma|theorem)\s+({NAME})"
)
REPORT = re.compile(
    r"'(.+)' (?:does not depend on any axioms|"
    r"depends on axioms: \[([^\]]*)\])"
)


def declarations(files):
    """Read the companion's top-level namespace/section and theorem headers."""
    names = []
    for file in files:
        scopes = []
        depth = 0
        for line in file.read_text().splitlines():
            # Exclude Lean nested comments and line comments from header matching.
            body = []
            for tok in re.split(r"(/-|-/|--)", line):
                if tok == "/-":
                    depth += 1
                elif tok == "-/" and depth:
                    depth -= 1
                elif not depth:
                    if tok == "--":
                        break
                    body.append(tok)
            text = "".join(body)
            scope = re.fullmatch(rf"(namespace|section)(?:\s+({NAME}))?\s*", text)
            if scope:
                kind, name = scope.groups()
                scopes.append((kind, name))
                continue
            if re.fullmatch(rf"end(?:\s+{NAME})?\s*", text):
                scopes.pop()
                continue
            header = HEADER.match(text)
            if header:
                parts = [n for kind, n in scopes if kind == "namespace"]
                names.append(".".join([*parts, header.group(1)]))
        if scopes or depth:
            raise ValueError(f"unclosed scope or comment in {file}")
    if not names or len(names) != len(set(names)):
        raise ValueError("expected a nonempty list of unique public theorem names")
    return names


def strict_prints(modules, names, work):
    source = work / "Audit.lean"
    source.write_text("\n".join([
        *(f"import {m}" for m in modules),
        *(f"#print axioms {n}" for n in names),
    ]) + "\n")
    response = subprocess.run(["lean", str(source)], capture_output=True, text=True)
    if response.returncode or response.stderr:
        raise ValueError(f"Lean audit failed\n{response.stdout}{response.stderr}")
    remaining = set(names)
    seen_axioms = set()
    for line in response.stdout.splitlines():
        result = REPORT.fullmatch(line)
        if not result or result[1] not in remaining:
            raise ValueError(f"unexpected or duplicate Lean output: {line}")
        remaining.remove(result[1])
        axioms = set(result[2].split(", ")) if result[2] else set()
        if extra := axioms - ALLOWED:
            raise ValueError(f"{result[1]} uses forbidden axioms: {sorted(extra)}")
        seen_axioms.update(axioms)
    if remaining:
        raise ValueError(f"no Lean report for {sorted(remaining)}")
    print(f"Checked {len(names)} public theorem roots across {len(modules)} modules. "
          f"Axioms used: {', '.join(sorted(seen_axioms)) or 'none'}.", flush=True)


def replay(modules, names, work, exporter, nanoda):
    config = work / "nanoda.json"
    config.write_text(json.dumps({
        "use_stdin": True, "permitted_axioms": sorted(ALLOWED),
        "unpermitted_axiom_hard_error": True, "unsafe_permit_all_axioms": False,
        "nat_extension": True, "string_extension": True,
    }))
    # Export only the proof roots and their transitive dependencies. Restricting
    # roots keeps unrelated declarations such as Init.sorryAx out of the export.
    with (work / "proofs.ndjson").open("w+b") as export:
        subprocess.run([exporter, *modules, "--", *names], stdout=export, check=True)
        if export.tell() == 0:
            raise ValueError("lean4export produced an empty proof export")
        export.seek(0)
        subprocess.run([nanoda, str(config)], stdin=export, check=True)
    print(f"Independent nanoda replay passed for {len(names)} roots.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("companion", type=Path)
    parser.add_argument("--lean4export", help="matching lean4export executable")
    parser.add_argument("--nanoda", help="nanoda_bin executable")
    args = parser.parse_args()
    if bool(args.lean4export) != bool(args.nanoda):
        parser.error("specify both --lean4export and --nanoda for independent replay")
    files = sorted(args.companion.resolve().glob("*.lean"))
    modules = [f.stem for f in files]
    names = declarations(files)
    with TemporaryDirectory(prefix="boolean-transfer-audit-") as temporary:
        work = Path(temporary)
        strict_prints(modules, names, work)
        if args.nanoda:
            replay(modules, names, work, args.lean4export, args.nanoda)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(str(exc))
