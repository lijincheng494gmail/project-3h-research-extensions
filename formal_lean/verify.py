"""Rebuild the projects and request a kernel axiom report for each public theorem."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(project, command):
    result = subprocess.run(command, cwd=project, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        raise SystemExit(f"{project.name}: {' '.join(map(str, command))}\n{result.stdout}")
    return result.stdout


def declared_names(source):
    scopes = []
    for line in source.read_text().splitlines():
        if match := re.match(r"^namespace\s+(\S+)", line):
            scopes.append(match[1])
        elif match := re.match(r"^end\s+(\S+)", line):
            if scopes and scopes[-1] == match[1]:
                scopes.pop()
        elif match := re.match(r"^(?:@\[[^\]]+\]\s*)?(?:theorem|lemma)\s+([^\s{(:]+)", line):
            yield ".".join([*scopes, match[1]])


def verify(number, fetch):
    project = ROOT / f"direction{number}"
    audit = project / "audit"
    audit.mkdir(exist_ok=True)
    sources = sorted(project.glob("*.lean"))
    names = [name for source in sources for name in declared_names(source)]
    if not names or len(set(names)) != len(names):
        raise SystemExit(f"{project.name}: missing or duplicate declarations")
    banned = re.compile(r"\b(?:sorry|admit|axiom|native_decide)\b")
    for source in sources:
        if banned.search(source.read_text()):
            raise SystemExit(f"Inspect placeholder, extra axiom, or native proof in {source.name}")
    if fetch:
        modules = sorted(set(re.findall(r"^import (Mathlib\.\S+)", "\n".join(
            source.read_text() for source in sources), re.M)))
        # Interpret the official cache client, also on hosts that cannot run its linked executable.
        run(project, ["lake", "build", "+Cache.Main"])
        run(project, ["lake", "env", "lean", "--run", ".lake/packages/mathlib/Cache/Main.lean",
                      "get", *modules])
    version = run(project, ["lake", "env", "lean", "--version"]) + run(project, ["lake", "--version"])
    build_log = run(project, ["lake", "build"])
    (audit / "build.log").write_text(version + "$ lake build\n" + build_log)
    commands = [f"import {source.stem}" for source in sources]
    commands.extend(f"#print axioms {name}" for name in names)
    with tempfile.TemporaryDirectory() as temp:
        entry = Path(temp) / "Inspect.lean"
        entry.write_text("\n".join(commands) + "\n")
        log = run(project, ["lake", "env", "lean", str(entry)])
    checked = {}
    for line in log.splitlines():
        if match := re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]+)\]", line):
            checked[match[1]] = set(match[2].split(", "))
        elif match := re.fullmatch(r"'([^']+)' does not depend on any axioms", line):
            checked[match[1]] = set()
    if set(checked) != set(names) or any(deps - ALLOWED for deps in checked.values()):
        raise SystemExit(f"{project.name}: incomplete or unexpected axiom report\n{log}")
    (audit / "axioms.log").write_text(log)
    extra = ""
    if number == 3:
        import sys
        extra = run(project, [sys.executable, "check_observations.py"])
        (audit / "source_check.log").write_text(extra)
    revisions = {}
    for dependency in json.loads((project / "lake-manifest.json").read_text())["packages"]:
        checkout = project / ".lake" / "packages" / dependency["name"]
        revision = run(checkout, ["git", "rev-parse", "HEAD"]).strip()
        if revision != dependency["rev"]:
            raise SystemExit(f"{checkout.name}: dependency differs from the lock file")
        revisions[dependency["name"]] = revision
    (audit / "dependencies.json").write_text(json.dumps(revisions, indent=2) + "\n")
    print(f"{project.name}: lake build passed; audited {len(names)} public theorems. {extra}".strip())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directions", type=int, choices=(1, 2, 3), nargs="*")
    parser.add_argument("--fetch-cache", action="store_true", help="download pinned Mathlib objects first")
    args = parser.parse_args()
    for index in args.directions or [1, 2, 3]:
        verify(index, args.fetch_cache)
