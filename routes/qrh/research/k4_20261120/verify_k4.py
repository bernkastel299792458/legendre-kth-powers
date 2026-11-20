"""Replay the conditional fourth-power certificate, from n=1 to infinity.

Run from any directory with the project's Python environment. The numerical
checks use the frozen moment tables and the analytic results cited in the proof.
Use --list to see the exact child commands, or --part to replay selected stages.
"""
import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING, localcontext
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
TABLE = "round8/zero_strip/early_green_rows.json"
NEAR = ",".join(
    f"round7/first_selected/companion_rows_{size}.json" for size in (100, 350, 600)
)
POLYGON = ("--high", "38", "--sub", "8", "--nh", "2", "--step", "6", "--n",
           "24", "--reuse", "5", "--near", NEAR)
SCALAR = ("--low", "29", "--high", "46", "--sub", "8", "--nh", "2", "--step",
          "8", "--table", TABLE)
SCRIPTS = {
    "witness": "legacy/code/certify_lower_range.py",
    "polygon": "round7/spatial/rotating_polygon.py",
    "phase": "round8/zero_strip/rotating_phase_bridge.py",
    "scalar": "round8/zero_strip/rotating_bridge.py",
    "tail": "round5/spectrum/height_budget.py",
}


@dataclass(frozen=True)
class Stage:
    name: str
    kind: str
    first: str
    last: str | None
    pieces: int
    options: tuple[str, ...]

    def command(self):
        args = [sys.executable, "-Bu", "-X", "utf8", SCRIPTS[self.kind]]
        if self.pieces:
            args.extend(("--first", self.first, "--last", self.last,
                         "--pieces", str(self.pieces)))
        if self.kind == "tail":
            args.extend(("--anchor", self.first))
        return args + list(self.options)


STAGES = (
    Stage("witnesses", "witness", "0", "109.46", 0, ("--verify",)),
    Stage("polygon-low", "polygon", "109.45", "114.45", 50, POLYGON),
    Stage("polygon-high", "polygon", "114.45", "115.45", 50, POLYGON),
    Stage("phase-low", "phase", "115.42", "116", 29, ("--reuse", "3")),
    Stage("phase-middle", "phase", "116", "120", 40, ("--reuse", "3", "--opt")),
    Stage("phase-high", "phase", "120", "121.5", 50, ("--reuse", "4")),
    Stage("scalar", "scalar", "121.5", "167.8", 463, SCALAR),
    Stage("tail", "tail", "167.8", None, 0,
          ("--polygon", "--short-core", "524288", "--last-node", "867")),
)

# Each child prints directed upper endpoints with an explicit decimal printing
# radius. Recheck the *upper* side of every printed enclosure using rationals.
NUM = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
BALL = rf"(?:\[{NUM} \+/- {NUM}\]|{NUM})"
CELL_LINES = {
    "polygon": rf"rotating polygon cell (\S+) (\S+) ({BALL})",
    "phase": rf"oscillatory rotation (\S+) (\S+) ({BALL})",
    "scalar": rf"(\S+) (\S+) full upper ({BALL})",
}
TOTAL_LINES = {
    "polygon": rf"whole rotating polygon bridge (\S+) (\S+) maximum ({BALL})",
    "phase": rf"complete bridge (\S+) (\S+) ({BALL})",
    "scalar": rf"complete scalar bridge (\S+) (\S+) upper ({BALL})",
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def strict_upper(value):
    if value.startswith("["):
        mid, radius = map(Fraction, value[1:-1].split(" +/- "))
        require(radius >= 0, "negative printing radius")
        upper = mid + radius
    else:
        upper = Fraction(value)
    require(0 < upper < 1, f"upper endpoint outside (0,1): {value}")
    return upper


def outward_decimal(upper):
    with localcontext() as ctx:
        ctx.prec = 18
        ctx.rounding = ROUND_CEILING
        return str(Decimal(upper.numerator) / Decimal(upper.denominator))


def validate_catalog():
    require(STAGES[0].first == "0" and STAGES[-1].last is None, "missing end")
    reached = Fraction(0)
    for stage in STAGES:
        require(Fraction(stage.first) <= reached, f"gap before {stage.name}")
        if stage.last is not None:
            end = Fraction(stage.last)
            require(end > reached, f"nonextending stage {stage.name}")
            reached = end
        require((ROOT / SCRIPTS[stage.kind]).is_file(), f"missing script {stage.name}")
    require(sum(s.pieces for s in STAGES) == 682, "default grid size changed")


def verify_output(stage, output):
    lines = output.splitlines()
    if stage.kind == "witness":
        data = json.loads(output)
        require(data["verified"] is True and data["small_witnesses_verified"] == 44721
                and data["effective_CHL_rows"] == 9, "missing prime witnesses or table rows")
        end = Fraction(data["target_L"])
        require(end == Fraction(stage.last)
                and data["n_max_inclusive"] >= data["target_n_max_inclusive"],
                "verified integer range does not reach the stated endpoint")
        check_integer_join(end, data["target_n_max_inclusive"] + 1)
        return f'{data["small_witnesses_verified"]} witnesses and the published table'

    start = Fraction(stage.first)
    if stage.kind == "tail":
        totals = [m for line in lines if (m := re.fullmatch(
            rf"L (\S+) grouped total ({BALL}) fixed {BALL}", line))]
        require(len(totals) == 1 and Fraction(totals[0][1]) == start,
                "missing infinite-range anchor")
        first = [int(m[1]) for line in lines if (m := re.fullmatch(r"first integer (\d+)", line))]
        require(len(first) == 1, "missing first integer on the half-line")
        check_integer_join(start, first[0])
        return "half-line, upper " + outward_decimal(strict_upper(totals[0][2]))

    end = Fraction(stage.last)
    width = (end - start) / stage.pieces
    rows = [m.groups() for line in lines
            if (m := re.fullmatch(CELL_LINES[stage.kind], line))]
    require(len(rows) == stage.pieces, f"{stage.name}: expected {stage.pieces} cell rows")
    ceilings = []
    for i, (left, right, value) in enumerate(rows):
        require(Fraction(left) == start + i * width and Fraction(right) == start + (i+1) * width,
                f"{stage.name}: wrong rational endpoints on cell {i+1}")
        ceilings.append(strict_upper(value))
    summaries = [m.groups() for line in lines
                 if (m := re.fullmatch(TOTAL_LINES[stage.kind], line))]
    require(len(summaries) == 1, f"{stage.name}: missing or duplicate final budget")
    left, right, value = summaries[0]
    require(Fraction(left) == start and Fraction(right) == end, "wrong final endpoints")
    # The per-cell and whole-stage ceilings can have different printing precision.
    ceilings.append(strict_upper(value))
    return f"{len(rows)} closed cells, upper {outward_decimal(max(ceilings))}"


def check_integer_join(endpoint, next_integer):
    from flint import arb, ctx
    with ctx.workprec(192):
        boundary = arb(endpoint.numerator) / endpoint.denominator
        require(next_integer > 1 and 4 * arb(next_integer - 1).log() < boundary
                < 4 * arb(next_integer).log(), "incorrect integer at logarithmic join")


def run(stage):
    # Several archived inner proofs use Python assertions. An optimized caller
    # or inherited PYTHONOPTIMIZE must never disable those checks in the child.
    env = os.environ.copy()
    env.pop("PYTHONOPTIMIZE", None)
    print("REPLAY", stage.name, f"[{stage.first}, {stage.last or 'infinity'}]", flush=True)
    cmd = stage.command()
    with subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                          text=True, encoding="utf8") as child:
        captured = []
        for line in child.stdout:
            print(line, end="", flush=True)
            captured.append(line)
        status = child.wait()
    if status:
        raise subprocess.CalledProcessError(status, cmd)
    print("VERIFIED", stage.name, verify_output(stage, "".join(captured)), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="print the proof parts and commands")
    parser.add_argument("--part", nargs="+", action="extend", choices=[s.name for s in STAGES],
                        help="replay one or more named parts (default: the complete chain)")
    args = parser.parse_args()
    validate_catalog()
    chosen = [s for s in STAGES if args.part is None or s.name in args.part]
    for stage in chosen:
        if args.list:
            print(f"{stage.name:15} [{stage.first}, {stage.last or 'infinity'}]",
                  f"{stage.pieces} closed cells" if stage.pieces else "")
            print("  " + subprocess.list2cmdline(stage.command()))
        else:
            run(stage)
    if not args.list:
        print("COMPLETE conditional k=4 certificate: all positive integers; 682 closed cells."
              if len(chosen) == len(STAGES) else "Selected parts verified.")


if __name__ == "__main__":
    main()
