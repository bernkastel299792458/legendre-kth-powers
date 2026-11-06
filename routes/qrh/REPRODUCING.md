# Reproducing the public review package

## Numerical argument

Use **Python 3.12.10** and python-flint 0.9.0 for the frozen replay. The
historical tail checker compares the full saved record, including the Python
patch version; another patch version can fail metadata equality even when
all numerical inequalities pass. CI pins 3.12.10 for that reason:

```sh
python -m pip install -r code/requirements.txt
python -X utf8 code/verify_k6.py --dry-run
python -X utf8 code/review_smooth_k6_refined.py
```

`verify_k6.py --dry-run` replays all four frozen certificates and checks exact
coverage and the global 6% CS coefficient test. `--dry-run` does not write a
summary. Without it, `verify_k6.py` writes a new
`results/k6_verification_summary.json`; `--output PATH` selects another output.
Each underlying `certify_*.py --verify` is read-only. Running those scripts
without `--verify` regenerates certificates and can change timestamps/hashes.

`review_smooth_k6_refined.py` independently reconstructs five critical middle cells at
512-bit precision and checks all 94 saved affine decompositions and coverage
metadata. It does not independently re-integrate all 94 cells.

## Lean and Mathlib

Install elan/Lean using the official Lean instructions. The pinned version is
`leanprover/lean4:v4.36.0-rc2`; the Mathlib commit and all transitive revisions
are recorded in `lean/lake-manifest.json`.

```sh
cd lean
lake update
lake exe cache get
lake build
lake env lean LegendreK6/Audit.lean
cd ..
python -X utf8 code/build_lean.py
```

The Python build driver compiles **every present local Lean module**, checks
the pinned dependency revisions, rejects local `sorry`, `admit`, custom
`axiom`, and `native_decide` shortcuts, and records the actual compiler output.
The proof-term audit and full theorem parameter types are written to
`kernel_axioms.txt` inside the selected fresh report directory. Existing
report directories are not overwritten; historical milestone records remain
separate. Preserve the original release manifest when comparing versions.

On the development machine, a pre-existing dependency cache was borrowed
read-only. A portable optional equivalent is:

```sh
python -X utf8 code/build_lean.py --dependency-root /absolute/path/to/.lake/packages
```

Only matching pinned revisions are accepted. Project `.olean` outputs go under the selected `--build-root` (by default
`lean/.lake/build/lib/lean`); no dependency sources or outputs are modified. The optional PowerShell helper
`code/run_lean.ps1` compiles an individual module with the same layout.

A successful build checks the current proof terms. Mathematical scope is
established by the complete type of `sixth_powers_from_named_inputs` and
its actual dependency audit. It has seven named external inputs and no
local analytic-segment or numerical-budget premise. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the current acceptance
state and the distinction from the stronger QRH/CS-only scope.

The milestone-1 proof-dependency diagnostic can additionally be reproduced:

```sh
cd lean
lake env lean ../audit/Milestone1Dependencies.lean
```

This inspects constants in actual local proof terms and checks that the
zero-count, real-axis, complex-power, arithmetic and six-term bound proofs
are used by the final tail theorem. It also prints the full external input
statements. This diagnostic does not replace Lean's kernel.

## Rebuild the generated proof terms

```sh
python -X utf8 code/generate_lean_certificates.py --check
```

This regenerates the finite source/data in a temporary directory and compares
bytes. The included `results/pratt_certificate_data.json` records proposed
factorizations and modular witnesses; Lean checks their use in the actual
primality proofs. The Python generator is not a primality oracle trusted by
the theorem. To intentionally regenerate the checked files, omit `--check`. The generator explicitly preserves CRLF in its generated source/data on all platforms; `.gitattributes` preserves exact release bytes.

## Paper

```sh
cd paper
python -X utf8 build_tex.py
xelatex -interaction=nonstopmode -halt-on-error main.tex
xelatex -interaction=nonstopmode -halt-on-error main.tex
```

Alternatively, Tectonic 0.17.0 with XeTeX-compatible packages can compile the
same source using `tectonic -X compile main.tex --keep-logs`. A CJK-capable
installation with ctex and Fandol fonts is required. PDF layout checks are
recorded separately; TeX compilation is not mathematical verification.

## Frozen sources and publication edits

`audit/source_snapshot_manifest.json` lists 13 byte-preserving copies of
the reviewed research artifacts. `audit/derived_sources.json` separately
records the adapted aggregate verifier, whose proof-document link now points
inside this publication package. The four core certificate programs and four
core JSON certificates retain their original mathematical-version hashes.
Historical review links refer to the original research directory, as explained
in `audit/source_reviews/README.md`.

`MANIFEST.json` hashes the release files. Check it **before** regeneration or
any command that deliberately rewrites reports:

```sh
python -X utf8 code/release_manifest.py --check
```

## Milestone 2 pilot

The difficult-cell proof has an additional actual-dependency diagnostic:

```sh
cd lean
lake env lean ../audit/Milestone2Dependencies.lean
cd ..
python -X utf8 code/generate_m2_pilot.py --all-blocks --check
python -X utf8 code/generate_m2_factor_bounds.py --check
python -X utf8 code/generate_m2_integer_data.py --check
```

The three generators propose explicit numerical witnesses and compare
regenerated source bytes. The final proof trusts Lean's checks of those
witnesses, not Python or Arb's assertions. Ordinary `decide +kernel` checks
the exact rational moment inequality; it does not use `native_decide`.

`audit/m2_pilot_numeric_build_2026-11-06.json` preserves the incremental
numerical build evidence and source hashes. Its initial enclosure builds
used Lean's default autoImplicit setting; the later connection/aggregation
builds used `autoImplicit=false`. This difference is disclosed in the record.
The native build driver now reads all lakefile Lean options; the PowerShell
helper passes the current `autoImplicit=false`. The final 241-module whole-tree build used the pinned Lake settings
and `autoImplicit=false` throughout. The existing 58-module aggregate report
predates M2 and must not be read as a clean rebuild of the expanded tree.

## Final downstream build and exact-input audit

The final theorem has seven named external mathematical inputs, documented in
FORMALIZATION_STATUS.md. To reproduce all local proof terms without reusing
project artifacts, choose a new output directory and a new report directory:

```sh
python -X utf8 code/build_lean.py --jobs 2 \
  --build-root "$PWD/lean/.lake/fresh-k6" \
  --report-root "$PWD/audit/builds/fresh-k6"
python -X utf8 code/run_dependency_audit.py \
  --build-report "$PWD/audit/builds/fresh-k6/lean_build_report.json" \
  --output-dir "$PWD/audit/builds/fresh-k6"
```

Use `--dependency-root` if borrowing a matching cache read-only. The driver
compiles every local module in dependency order, with all lakefile Lean
options, and records source/artifact hashes before and after compilation.
Reports now go to a fresh run directory; the old top-level 58-module report
remains historical M1 evidence. The audit helper verifies all current hashes
and uses exactly the new build's library search path. Its output prints the
complete theorem types and actual transitive proof dependencies.

Exact rational kernel reduction currently has a high-memory module. A
32 GiB or larger development environment is advisable; a recorded Windows
trial reached about 21.4 GiB working set. A literal-data performance experiment
did not improve this and was reverted; its failure/restoration record is
retained. `--jobs 1` reduces concurrent memory demand. Hosted CI additionally
provisions an 8 GiB swap file on its disposable runner; a CI success is only
claimed for the actual run and revision recorded, not predicted from this
configuration. GitHub's current standard public Linux specification is
[16 GB RAM and 14 GB SSD](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

The far proof generators have the same read-only check interface:

```sh
python -X utf8 code/generate_m3_far.py --all-blocks --check
python -X utf8 code/generate_m3_far_factor_bounds.py --check
python -X utf8 code/generate_m3_far_integer_data.py --check
```

The lower-middle table is the exact Lean `mapIdx` of the earlier rows; its
new rational inequality is checked directly in the kernel. There is no
additional lower-middle external data generator in the accepted source.

## Accepted local run

The published clean run is [final-20261106](audit/builds/final-20261106/lean_build_report.json):
241/241 modules, 2690.618 seconds, followed by the matching 17.375-second
[dependency audit](audit/builds/final-20261106/final_dependency_report.json).
Do not reuse its output directory for a fresh reproduction. The final
checkpoint and release manifest distinguish the completed seven-input
proof from the stronger, unclaimed QRH/CS-only scope. Manifest checks are
portable and do not require the publisher's absolute Windows paths or
local compiled artifacts to exist on the reproducing machine.
