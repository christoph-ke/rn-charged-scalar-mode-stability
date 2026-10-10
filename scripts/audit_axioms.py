#!/usr/bin/env python3
"""Print and check the transitive axioms of all 20 source-facing theorem anchors."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ANCHORS = (
    'ModeStability.radiusOf_spec',
    'ModeStability.spherical_real_mode_exclusion',
    'ModeStability.separation_at_corotation',
    'ModeStability.exact_reduction',
    'ModeStability.coefficient_inequalities',
    'ModeStability.dephased_current',
    'ModeStability.flux_identity',
    'ModeStability.AllAngular.real_mode_exclusion',
    'ModeStability.AllAngular.complementaryBandExclusion_holds',
    'ModeStability.AllAngular.spherical_real_mode_exclusion_unconditional',
    'ModeStability.AllAngular.common_geometry',
    'ModeStability.AllAngular.scalar_positivity',
    'ModeStability.AllAngular.angular_positivity',
    'ModeStability.AllAngular.zero_frequency_exclusion',
    'ModeStability.AllAngular.horizon_solution_existsUnique',
    'ModeStability.AllAngular.infinity_solution_existsUnique',
    'ModeStability.AllAngular.horizon_solution_continuous',
    'ModeStability.AllAngular.infinity_solution_continuous',
    'ModeStability.AllAngular.source_solution_existsUnique',
    'ModeStability.AllAngular.inhomogeneous_estimate',
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check_output(output: str) -> None:
    found = {}
    pattern = re.compile(
        r"^'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|"
        r"does not depend on any axioms)[ \t]*$", re.MULTILINE)
    for match in pattern.finditer(output):
        name, raw = match.groups()
        axioms = set((raw or "").replace(",", " ").split())
        if name in found:
            raise ValueError(f"duplicate axiom output: {name}")
        found[name] = axioms
        unexpected = axioms - ALLOWED
        if unexpected:
            raise ValueError(f"{name}: forbidden axioms: {', '.join(sorted(unexpected))}")
    if set(found) != set(ANCHORS):
        missing = sorted(set(ANCHORS) - set(found))
        extra = sorted(set(found) - set(ANCHORS))
        raise ValueError(f"incomplete anchor audit; missing={missing}, unexpected={extra}")


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    lake_dir = root / ".lake"
    lake_dir.mkdir(exist_ok=True)
    # A transient probe keeps the expensive commands out of ordinary modules.
    with tempfile.TemporaryDirectory(prefix="axiom-audit-", dir=lake_dir) as temporary:
        probe = Path(temporary) / "Audit.lean"
        probe.write_text("import ModeStability\n\n" +
                         "".join(f"#print axioms {name}\n" for name in ANCHORS))
        try:
            result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root,
                                    capture_output=True, text=True, check=False)
        except OSError as error:
            print(f"FAIL: cannot run Lean: {error}", file=sys.stderr)
            return 1
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    if result.returncode:
        print(f"FAIL: Lean exited with status {result.returncode}", file=sys.stderr)
        return 1
    try:
        check_output(result.stdout)
    except ValueError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(f"PASS: all {len(ANCHORS)} theorem anchors use only propext, Classical.choice, Quot.sound.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
