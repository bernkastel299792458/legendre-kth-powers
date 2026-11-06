# Build driver and fresh-artifact audit review

Date: 2026-11-06. This review covers the build infrastructure, not a new
mathematical proof or an executed GitHub Actions run.

The reviewing Codex worker implemented `code/build_lean.py`, so its assessment
of that file is a **self-review**. The worker did not write
`code/run_dependency_audit.py` or `.github/workflows/qrh.yml`; the interface and
source inspection of those files is a **cross-review within the same Codex
research team**, not independent external peer review.

## Scope and result

The reviewed driver/helper/CI interfaces are consistent. Small actual-Lean
fixtures passed the scheduling and evidence checks below. A read-only scan of
the then-current project found 241 modules with a valid dependency order.
This review did **not** launch a full project rebuild. A final clean build and
its resulting dependency-audit report remain separate run evidence.

The driver compiles Lean source using the selected Lean executable. The
`FinalDependencies.lean` diagnostic subsequently inspects the actual theorem
types and proof terms and prints their axiom dependencies. That diagnostic
does not replace Lean's kernel, prove the named external inputs, or establish
mathematical correctness merely by finding declaration names. The retained
`end_to_end_H1_H2_formalization: false` flag distinguishes a proof relative to
the complete named literature inputs from a stronger QRH/CS-only claim. See
[FORMALIZATION_STATUS.md](../FORMALIZATION_STATUS.md).

## Driver self-review and actual smoke evidence

The driver supports `--jobs N` (default 1), `--build-root PATH` (default the
existing project build directory), repeatable `--module MODULE`, and
`--report-root PATH`. Without an explicit report path it creates a unique
directory under `audit/builds/` and prints `REPORT_ROOT=...`. An existing report
directory is rejected. Existing milestone reports are not overwritten.

The scheduler submits a module only after every selected local dependency has
returned `PASS`. Independent modules may run concurrently. On the first
failure it stops submitting new work and waits for already-running jobs;
unstarted modules are explicitly recorded. Final JSON rows and the collected
log follow the deterministic topological order, regardless of completion
order. Interrupt handling targets subprocess objects owned by this build.
There is no recursive deletion or mutation of the borrowed dependency cache.

The selected output root is first on `LEAN_PATH`. Remaining entries are the
build libraries of manifest-listed dependency packages, whose Git revisions
are checked. The development output tree and source tree are not appended as
fallback project libraries. A fresh output root therefore prevents old local
oleans from satisfying local imports. The driver always compiles the selected
closure; artifact existence alone is not treated as success.

Each compiled row records its command, working directory, source hash at
discovery and before/after compilation, source stability, output path and olean
hash. Final source and artifact hashes are checked again after scheduling.
The report records the full `leanOptions` parsed with `tomllib`, option
arguments, toolchain/version, manifest and lakefile hashes, verified revisions,
search path, output/report roots, worker count and preflight commands.

Actual smoke command:

```powershell
python -B routes/qrh/lean/.lake/tmp/build_driver_smoke.py
```

The temporary harness used real Lean 4.36.0-rc2, `-DautoImplicit=false`, two
workers and newly created output directories. It changed only temporary
fixtures; no project mathematical source was rebuilt or modified.

| Case | Observed result |
|---|---|
| Independent A/B, with C importing both | A and B overlapped; C started only after both succeeded; all three passed. |
| Deliberately invalid B while A was running | B failed; C was `NOT_STARTED` and had no olean; A completed successfully after B's failure. |
| Source edited after its subprocess started | Source hash change caused `FAILED`, even though compilation could otherwise complete. |
| Output requested inside the dependency cache | Rejected as `PREFLIGHT_FAILED`; no output directory was created there. |
| Stable evidence order | Reports and logs remained ordered A, B, C although B finished first. |
| Historical evidence preservation | The existing M1 `lean_build_report.json` hash was unchanged. |

The concise evidence, including fixture source/artifact hashes and timestamps,
is [build_driver_smoke.json](build_driver_smoke.json). Temporary raw reports
were retained locally under `lean/.lake/tmp/build-driver-smoke-klofewtc/`.
They are not Lean source modules included in publication or the full build.

## Dependency helper and CI cross-review

The helper consumes the driver's `lean_executable`, `option_args`, `lean_path`,
`output_root`, module inventory and hash fields without a stale default build
path. Before and after running the diagnostic it checks the successful full
build status, current module inventory, current project source/artifact hashes,
artifact containment within the selected build root, and the lakefile/manifest
hashes. The fresh build root must be first in the recorded search path. It
also binds the diagnostic source and diagnostic output to SHA256 values.

One report-binding issue was identified and **resolved during review**: the
helper now reads the build-report bytes once, hashes exactly those parsed
bytes, verifies the report file is unchanged at the end, and records the
originally read hash. This avoids associating a diagnostic with a later
replacement report. The final reviewed helper hash is listed below.

An initial preflight rejection intentionally exits nonzero before writing a
dependency-audit report. Once the diagnostic runs, its ordinary failure paths
write `AUDIT_FAILED`. In the reviewed CI, fresh paths and `set -euo pipefail`
prevent a rejected run from uploading an old successful dependency report.

CI passes explicit `$RUNNER_TEMP/k6-clean-lib` and
`$RUNNER_TEMP/k6-clean-audit` paths with `--jobs 1`, and invokes the helper on
that exact report directory. Subsequent assertions and artifact copying read
those fresh paths. They require successful rows, no preexisting local oleans,
the current final theorem marker and a passed dependency report. The workflow
also includes the finalized lower-integer generator's `--check` command.
The helper's four exact axiom-output patterns were compared with the existing
incremental diagnostic output and matched; this was a text-parser check, not
a rerun of the full proof.

## Pinned Lean action: cache preparation with project build disabled

The official action source was read at commit
`fe408643ea7367d8c0404a8be3975bb145f5fb64`. Its Elan setup step is independent
of `build`; the setup script invokes `lean --version` and `lake --version`
from the package directory. The Mathlib-cache step is separately controlled
by `use-mathlib-cache` and runs `lake exe cache get` when explicitly true.
The project build step alone uses the configured build flag. Thus the current
`build: "false"`, `auto-config: "false"`, `use-mathlib-cache: "true"`
combination still prepares the selected toolchain and dependency cache. No
extra project `lake build` is needed. Sources:
[pinned action](https://github.com/leanprover/lean-action/blob/fe408643ea7367d8c0404a8be3975bb145f5fb64/action.yml#L219),
[pinned Elan setup](https://github.com/leanprover/lean-action/blob/fe408643ea7367d8c0404a8be3975bb145f5fb64/scripts/install_elan.sh),
[pinned feature configuration](https://github.com/leanprover/lean-action/blob/fe408643ea7367d8c0404a8be3975bb145f5fb64/scripts/config.sh).

This confirms the action's configured control flow. It does not assert that a
future network download or hosted CI run has already succeeded.

## Reviewed source snapshots

Paths are relative to `routes/qrh/` except the shared workflow.

| Source | SHA256 |
|---|---|
| `code/build_lean.py` | `8a438e435ca901ff4b0c9181ee418b4ad3740fcf7db9b23b52867e5dc6f85fd0` |
| `code/run_dependency_audit.py` | `19f8dec62c6081cbc093baa03c45d8361bea603c623bcf9cf38d8db9b9fee272` |
| `.github/workflows/qrh.yml` | `3c8ae3f5ed5ce23618049e5a96d9d26f8ea19fcc417f8127e73dad9c9aebb892` |
| `audit/FinalDependencies.lean` | `2180d7708aec8aa57ec201b9a1f72ec0f47025ed58a2e082c75d86a550f6308a` |

The helper, workflow and diagnostic were only read by this reviewer. Their
author made the reported fixes. Subsequent edits require a new snapshot or an
explicit review addendum; this report does not silently certify later bytes.

## Root integration follow-up

After the worker review, the root removed the abandoned lower literal-data
generator check and added an 8 GiB swap-file setup on the disposable Linux
CI runner. The accepted Lean sources and driver/helper interfaces are unchanged.
Root validation parsed the workflow with PyYAML 6.0.2, checked every Lean-job
run block with Git Bash `bash -n`, and checked 145 local documentation links;
all passed. No Linux CI execution is claimed by those static checks.

Current workflow SHA256: `c29d4546b19639994187c47b08087d39badeba1a2f0dc798356d751a8153634c`.

## Release metadata follow-up: worker cross-review

The worker read, but did not implement, the updated `code/release_manifest.py`.
Reviewed SHA256: `0db887a1be9425a7c2cf038031483356d711e9208d20549c1b6babaa16f406f6`.

The new downstream-completion flag is separate from the retained false
QRH/CS-only flag. Its scope names the exact final theorem and all seven Lean
inputs, and explicitly states that the external inputs were not reproved.
Acceptance requires the completed checkpoint, matching build/audit evidence
hashes, successful full-build and audit statuses, fresh-output flags, the
complete current Lean source inventory and hashes, the diagnostic source and
output hashes, and the current toolchain/configuration. A missing checkpoint
returns `not_accepted`; this branch was checked without writing the manifest.

Portability is preserved: current source checks use `source_relative` under
the release's own Lean directory. The release helper does not dereference the
publisher's absolute source/build directories or require local olean files.
Checking those actual artifacts belongs to the fresh build and its matching
dependency audit. This helper manages portable evidence and scope metadata;
it does not replace Lean's kernel or independently prove the mathematical
conclusion.

Both nonblocking review suggestions were implemented and reread: `--check`
now verifies the explicit v2 schema as well as the complete scope metadata,
and each build/audit evidence file is read once into bytes that are both
hashed and parsed. Thus the evidence identifier and interpreted report use
the same snapshot. The checkpoint is bound through the release file-hash map,
without a circular dependency on the manifest's own hash.

No full build, dependency diagnostic or release-manifest generation was run
for this follow-up. Final acceptance remains the responsibility of the actual
completed build, audit and checkpoint evidence.

## Final fresh-build verification: worker follow-up

The completed final build and matching dependency diagnostic were independently
re-hashed on 2026-11-06. All **241 source files and 241 olean artifacts** matched
every recorded hash stage; the complete source-inventory SHA256 remained
`8cdd61ce151a0dc97092d88b030e5d47cd95bc902d8c44fe0b98e5f670cc18f6`,
equal to the worker's snapshot taken during the frozen build. There were
**2,910 successful consistency checks and no failures**. The detailed record is
[final_build_independent_check.json](final_build_independent_check.json), SHA256
`25d05acd28e8e653baff3d896fbc984c73f62111b749ea1c99d5d8c9d12675f8`.

The checks confirmed the exact fresh output directory, the false preexisting-root
and preexisting-artifact flags, both workers, every actual compiler command,
`autoImplicit=false`, Lean `v4.36.0-rc2`, current dependency Git revisions,
configuration hashes, dependency ordering and compile timestamps. The search path
contained only this fresh local output and the manifest-listed dependency
libraries. The final build took 2,690.618 seconds. No project source or recorded
artifact was altered, and this verification did not launch another compilation.

The dependency audit binds to the exact build-report bytes with SHA256
`bddf96be2d66f280e0bb8ace907967393d606bb5b49808bff99d793c389dcf43`.
Its diagnostic source, output, command and search path also matched. The four
printed final theorem axiom lists contained only `propext`, `Classical.choice`
and `Quot.sound`; the final theorem type explicitly retained all seven named
external inputs and concluded the actual strict prime interval between sixth
powers. The proof-term dependency marker was present.

This additional checker used direct filesystem reads and subprocess version/Git
queries, without importing the build driver or audit helper. Its source is
retained locally under `lean/.lake/tmp/final_build_independent_verify.py`, and
its hash and all 241 re-read source/artifact hashes are recorded in the JSON.
The worker authored the build driver, so this remains a disclosed self-review
of that implementation and a cross-check of the root's final run. It is not
independent external mathematical peer review. These metadata checks and the
proof-term diagnostic do not replace Lean's kernel or reprove the seven external
inputs.
