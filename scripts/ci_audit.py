#!/usr/bin/env python3
"""Automated verification suite (used locally and in GitHub Actions CI):
  1. Static Lean 4 zero-cheating scan (no sorry/admit/custom axiom/native_decide/ofReduceBool).
  2. Standalone Lean 4.16.0 `lake build` + `#print axioms` verification.
  3. Strict RFC-8259 JSON validation (rejecting NaN/Infinity), CSV integrity, and Python syntax check.
"""

from __future__ import annotations

import json
import os
import py_compile
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean_proofs"
LEAN_FILE = LEAN_DIR / "DiamondProofs/Paper2_Subordination.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

FORBIDDEN_PATTERNS = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"^\s*axiom\b", "custom axiom declaration"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bLean\.ofReduceBool\b", "Lean.ofReduceBool"),
    (r"^\s*unsafe\b", "unsafe declaration"),
    (r"@\[implemented_by", "implemented_by attribute"),
    (r"@\[extern", "extern attribute"),
    (r"^\s*partial\s+def\b", "partial def"),
]


def strip_lean_comments(src: str) -> str:
    # Remove block comments /- ... -/ (including docstrings) and line comments -- ...
    out = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    out = re.sub(r"--[^\n]*", "", out)
    return out


def reject_nonstandard_json(token: str) -> None:
    raise ValueError(f"Non-RFC-8259 JSON token detected: {token}")


def main() -> None:
    print(f"[1/4] Static Lean 4 soundness scan: {LEAN_FILE.relative_to(ROOT)}")
    raw = LEAN_FILE.read_text(encoding="utf-8")
    code_only = strip_lean_comments(raw)
    for pat, label in FORBIDDEN_PATTERNS:
        m = re.search(pat, code_only, flags=re.MULTILINE)
        if m:
            raise RuntimeError(f"Forbidden Lean construct ({label}) found: {m.group(0)!r}")
    print(f"  [PASS] {len(raw.splitlines())} lines clean (0 sorry, 0 custom axioms, 0 native_decide).")

    print(f"\n[2/4] Building Lean 4.16.0 module DiamondProofs.Paper2_Subordination & auditing axioms")
    env = {**os.environ, "PATH": f"{Path.home() / '.elan' / 'bin'}:{os.environ.get('PATH', '')}"}
    res = subprocess.run(
        ["lake", "build", "DiamondProofs.Paper2_Subordination"],
        cwd=LEAN_DIR,
        env=env,
        capture_output=True,
        text=True,
    )
    if res.returncode != 0:
        print(res.stdout)
        print(res.stderr, file=sys.stderr)
        raise RuntimeError(f"lake build failed with exit code {res.returncode}")
    combined = res.stdout + "\n" + res.stderr
    if "warning:" in combined.lower() or "error:" in combined.lower():
        raise RuntimeError(f"Lean compiler warnings/errors detected:\n{combined}")

    axiom_lines = [ln for ln in combined.splitlines() if "depends on axioms:" in ln or "does not depend on any axioms" in ln]
    for ln in axiom_lines:
        m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", ln)
        if m:
            used = {tok.strip() for tok in m.group(1).split(",") if tok.strip()}
            bad = used - ALLOWED_AXIOMS
            if bad:
                raise RuntimeError(f"Disallowed axioms {bad} in line: {ln}")

    # Exhaustive Lean 4 kernel axiom audit over EVERY public theorem in the module
    meta_audit = (
        "import Lean\n"
        "import DiamondProofs.Paper2_Subordination\n"
        "open Lean in\n"
        "#eval show CoreM Unit from do\n"
        "  let env ← getEnv\n"
        "  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]\n"
        "  let mut nPub := 0\n"
        "  let mut nZero := 0\n"
        "  let mut nBad := 0\n"
        "  for (n, info) in env.constants.toList do\n"
        "    if (n.toString.startsWith \"DiamondProofs.Paper2.\") && !isPrivateName n then\n"
        "      match info with\n"
        "      | .thmInfo _ =>\n"
        "        nPub := nPub + 1\n"
        "        let axs ← Lean.collectAxioms n\n"
        "        if axs.isEmpty then nZero := nZero + 1\n"
        "        for a in axs do\n"
        "          if !(allowed.contains a) then\n"
        "            nBad := nBad + 1\n"
        "            IO.println s!\"DISALLOWED_AXIOM {n}: {a}\"\n"
        "      | _ => pure ()\n"
        "  IO.println s!\"KERNEL_PUBLIC_THEOREMS={nPub} ZERO_AXIOM={nZero} DISALLOWED_AXIOMS={nBad}\"\n"
    )
    res_ax = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=meta_audit,
        cwd=LEAN_DIR,
        env=env,
        capture_output=True,
        text=True,
    )
    if res_ax.returncode != 0 or "DISALLOWED_AXIOMS=0" not in res_ax.stdout:
        raise RuntimeError(f"Kernel axiom audit failed:\n{res_ax.stdout}\n{res_ax.stderr}")
    summary_line = [ln for ln in res_ax.stdout.splitlines() if "KERNEL_PUBLIC_THEOREMS=" in ln][-1]
    print(f"  [PASS] lake build succeeded cleanly (0 warnings, {len(axiom_lines)} #print axioms; {summary_line}).")

    print(f"\n[3/4] Validating strict RFC-8259 JSON, CSV datasets, and Python syntax")
    json_count = 0
    csv_count = 0
    for fp in sorted((ROOT / "data").iterdir()):
        if fp.suffix == ".json":
            json.loads(fp.read_text(encoding="utf-8"), parse_constant=reject_nonstandard_json)
            json_count += 1
        elif fp.suffix == ".csv":
            lines = fp.read_text(encoding="utf-8").splitlines()
            if len(lines) < 2:
                raise RuntimeError(f"Empty CSV dataset: {fp.name}")
            csv_count += 1
    py_count = 0
    for fp in sorted((ROOT / "src").glob("*.py")):
        py_compile.compile(str(fp), doraise=True)
        py_count += 1
    print(f"  [PASS] {json_count} strict RFC-8259 JSON files, {csv_count} CSV tables, {py_count} Python scripts verified.")

    print("\n[4/4] Running scientific numerical unit test: src/test_mpmath_core.py")
    res_t = subprocess.run([sys.executable, "src/test_mpmath_core.py"], cwd=ROOT, check=False)
    if res_t.returncode != 0:
        raise RuntimeError("Unit test failed: src/test_mpmath_core.py")
    print("  [PASS] Unit test passed.")

    print("\nALL VERIFICATION CHECKS PASSED.")


if __name__ == "__main__":
    main()
