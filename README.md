# Primes between consecutive k-th powers

**English** | [简体中文](README.zh-CN.md)

**AI authors: Claude and Codex.** Claude leads the traditional route; Codex
leads the QRH(7/8) route. [Authorship](AUTHORS.md) · [Collaboration protocol](RESEARCH_PROTOCOL.md)

This repository studies when, for **every integer n >= 1**, the open interval
`(n^k, (n+1)^k)` contains a prime. It contains two research tracks with
different mathematical premises, separate review packages, and separate
verification records.

**Status — 2026-11-06:** public review drafts, produced largely by AI systems.
Neither track has a recorded complete human expert review. The QRH track
has completed its full downstream Lean proof from seven named inputs: all
241 modules passed an isolated rebuild and the matching dependency audit. The
traditional track retains the verification scope stated below.

## Results at a glance

Every row below concerns **all positive integers n**, under the stated inputs
and the new arguments in its manuscript.

| Research track | Reported result | Main premises | Review package |
|---|---|---|---|
| **A. Traditional explicit estimates** | Every integer **k >= 70** | The listed explicit estimates, including the **4.896** zero-free-region constant from the Bellotti–Trudgian–Yang preprint. No QRH assumption. | [Traditional manuscript, English](routes/traditional/proof/manuscript.md) |
| **A. Traditional, refereed-input variant** | Every integer **k >= 74** | The listed refereed literature inputs, using **5.558691** in place of 4.896. No QRH assumption. | [Traditional review package](routes/traditional/proof/README.md) |
| **B. Assuming QRH(7/8)** | Fixed exponent **k = 6** | **H1:** every nontrivial zeta zero has real part at most 7/8. **H2:** CS **arXiv:2507.15184v2**, Corollary 1 and the specified table rows, plus the cited auxiliary inputs. | [QRH route package](routes/qrh/README.md) · [Chinese paper, PDF](routes/qrh/paper/main.pdf) |

“Refereed-input” describes the sources used by that variant; it does not mean
that this project's new proof has been peer-reviewed. The two tracks answer
the question under different premises, so their exponents should be read
with those premises attached.

## Track A — traditional explicit estimates

### Result and method

The [v4 manuscript](routes/traditional/proof/manuscript.md) gives computer-assisted arguments for
all integer exponents **k >= 70**, and for **k >= 74** when restricting the
literature inputs to refereed results.

The method combines explicit zero-free regions, hybrid zero-density bounds,
a smoothed explicit formula, finite-range certificates, and an analytic
infinite tail. It does **not** assume QRH(7/8).

The k >= 70 variant uses the preprint constant 4.896. The project's
[AI audit](routes/traditional/proof/zfr_audit/bty_4.896/REPORT.md) reports that its proof closes
after specified corrections; this is not human peer review. The k >= 74
variant uses the refereed constant 5.558691. Both variants also use 21.233,
54.004, and the other inputs stated in the manuscript.

### Evidence and limits

Arb certificates cover the numerical ranges. Lean checks the logical assembly
of the ranges **assuming the stated analytic estimates and certificate
conclusions**. It does not prove those analytic estimates or Arb computations.
See the [review checklist](routes/traditional/proof/REVIEW_CHECKLIST.md),
[recorded numerical replay](routes/traditional/proof/certificates/verify_all_output.txt), and
[Lean scope](routes/traditional/proof/README.md#lean-证明了什么).

The input checks and open review tasks remain visible in
[SOURCES.md](routes/traditional/SOURCES.md), [input verification](routes/traditional/proof/input_verification/), and
[zero-free-region audits](routes/traditional/proof/zfr_audit/README.md). In particular, the
Bellotti table was checked against arXiv v2; comparison with the printed
journal table remains a review task.

**The earlier k >= 67 claim was withdrawn.** The project's audit found an
arithmetic problem in the thesis proof of the required constant 19.62.
The finding is the project's reading, not an author-confirmed correction.
See the [audit report](routes/traditional/proof/zfr_audit/thesis_19.62/REPORT.md) and
[withdrawn certificates](routes/traditional/proof/certificates/withdrawn_k67/README.md).
The historical Lean package name `LegendreK67` is not a current k = 67 claim.

## Track B — assuming QRH(7/8)

### Result and explicit premises

We adopt QRH(7/8) as this track's starting point because OpenAI has released
its [September 30, 2026 proof manuscript on the 7/8 zero-free half-plane](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)
and accompanying Lean materials in the [official openai/math repository](https://github.com/openai/math).
We take its bound on nontrivial zeta zeros as an explicit upstream input and
investigate the resulting prime intervals between consecutive powers.

OpenAI's [Family 003 documentation](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md) specifies the scope of its
7/8 formalization. We have not independently rebuilt its complete dependencies
or run the upstream Comparator, so H1 remains explicit in our theorem statements.
That upstream formalization is distinct from this project's downstream
prime-interval proof, whose exact inputs and build status are listed below.

This track also explicitly assumes the
Chourasiya–Simonič **v2** density result, treated as a preprint dependency:
Corollary 1, Table 1 rows indexed **16–27** (the first 12 rows), on their
specified domains. The cited classical auxiliary inputs are listed in the
[paper](routes/qrh/paper/manuscript.md).

Under these inputs, the written argument gives, for every integer n >= 1, a prime

```text
n^6 < p < n^6 + 6n^5 < (n+1)^6.
```

The result is conditional on **both H1 and H2**, not on QRH alone. The project
has not obtained an all-n result for k = 4 or k = 3; those remain the stage
and longer-term research targets respectively.

### Evidence and limits

The package combines 1259 small-range prime witnesses and CHL interval rows,
**94** middle cells, **60** further cells, and an analytic infinite tail.
The refined middle bound is at most `0.939735996783828324763044`. With all
other inputs, exponents, and domains fixed, uniformly increasing all three
CS coefficient columns by **6%** still passes the written proof chain.
That sensitivity check does not validate the CS theorem itself.

The final Lean theorem `sixth_powers_from_named_inputs` has compiled with type

```text
QRHSevenEighths -> CSv2 -> RosserZeroCount -> IntegratedExplicitFormula ->
  FiniteRH3e12 -> CHJIIShortInterval -> CHLRows -> SixthPowerConclusion
```

All project-specific analytic segments and numerical budgets are proved.
There is no local prime-interval or certificate-correctness premise in this
final type. The proof covers every point of the 94 middle and 60 far cells,
plus the integer lower range and infinite tail. The far formal argument uses
a new trapezoid certificate; the historical polynomial proof is preserved.
The original 6% coefficient-sensitivity result is not automatically a property
of the new conservative formal lower-range bound.

See the [readable formalization addendum](routes/qrh/paper/lean_formalization_addendum.md),
[final theorem source](routes/qrh/lean/LegendreK6/FinalResult.lean), and
[exact formalization status](routes/qrh/FORMALIZATION_STATUS.md).
The [clean 241-module build](routes/qrh/audit/builds/final-20261106/lean_build_report.json)
and [matching proof-dependency audit](routes/qrh/audit/builds/final-20261106/final_dependency_report.json)
both passed, with only the standard Lean axioms. This is
a complete downstream proof relative to all seven named inputs, not a
re-proof of the auxiliary literature or a QRH/CS-only theorem.

The earlier [Linux CI run](https://github.com/bernkastel299792458/legendre-kth-powers/actions/runs/42153017737)
at `58521b6` remains historical evidence for its original partial scope.
It is not presented as a build of these new sources.

## Read, reproduce, and review

| Purpose | Traditional track | QRH track |
|---|---|---|
| Read the argument | [English manuscript](routes/traditional/proof/manuscript.md) | [Original manuscript](routes/qrh/paper/manuscript.md) · [Formal proof addendum](routes/qrh/paper/lean_formalization_addendum.md) |
| Inspect dependencies | [Manuscript §3](routes/traditional/proof/manuscript.md) · [Sources](routes/traditional/SOURCES.md) | [Paper §1](routes/qrh/paper/manuscript.md) · [BibTeX](routes/qrh/paper/references.bib) |
| Reproduce computations | [Review package](routes/traditional/proof/README.md#如何复核) | [Reproduction instructions](routes/qrh/REPRODUCING.md) |
| Understand Lean coverage | [Assembly scope](routes/traditional/proof/README.md#lean-证明了什么) | [Exact theorem and acceptance evidence](routes/qrh/FORMALIZATION_STATUS.md) |
| Review the evidence | [Checklist](routes/traditional/proof/REVIEW_CHECKLIST.md) · [AI reviews and responses](routes/traditional/review/) | [Scope review](routes/qrh/audit/PUBLICATION_SCOPE_REVIEW.md) · [Historical reviews](routes/qrh/audit/source_reviews/README.md) |

For the **traditional numerical replay**, run from the repository root:

```sh
python -m pip install -r routes/traditional/proof/code/requirements.txt
python routes/traditional/proof/code/verify_all.py
```

For the **QRH numerical replay**, use **Python 3.12.10** and run from the
repository root. The frozen tail checker includes the Python patch version
in its metadata comparison.

```sh
python -m pip install -r routes/qrh/code/requirements.txt
python routes/qrh/code/release_manifest.py --check
python -X utf8 routes/qrh/code/verify_k6.py --dry-run
python -X utf8 routes/qrh/code/generate_lean_certificates.py --check
```

Both packages use python-flint 0.9.0. Their linked instructions give the
separate Lean build procedures and further review commands. A green CI run,
absence of `sorry`, or standard-axioms-only output must be read together with
the complete theorem hypotheses. Problems can be reported through
[GitHub Issues](https://github.com/bernkastel299792458/legendre-kth-powers/issues),
identifying the track, file or theorem, and version.

## Human direction and AI contributions

| Role | Recorded contribution |
|---|---|
| **Project owner** | Set the problem, research directions, quality requirements, audit requests, and publication decisions. Has not independently verified the mathematics. |
| **Codex — topic selection** | Helped identify Legendre-type questions as a research target. |
| **Claude — traditional track** | Developed the literature review, arguments, code, certificates, Lean assembly, and manuscript. Separate sessions audited constants and translated the conversation. |
| **Codex and a separate Claude instance — traditional reviews** | Supplied the AI reviews and associated checks archived under `routes/traditional/review/`. |
| **Codex — QRH track** | Developed the conditional argument, refined certificates, Lean components, manuscript, and reproducibility package, with cross-checks in separate agent contexts. |
| **Claude — earlier QRH review** | Reviewed the earlier 76-cell version; its recommendations prompted clearer CS v2 premises and stronger numerical margins. That review does not certify the later Lean implementation. |

AI agreement is not a substitute for mathematical proof or human expert
review. The traditional manuscript contains its detailed contribution
statement and [conversation archive](routes/traditional/proof/conversation/); the QRH package
has a separate [AI-use statement](routes/qrh/AI_USE.md). Human author
names, affiliations, and emails remain unfilled in the QRH paper.

## Repository map and licenses

Research is organized by **route**, not by an exponent. Result-specific names
such as `LegendreK6` and the historical `LegendreK67` namespace remain inside
proof implementations so that audited mathematical source bytes stay stable.
The traditional Lean project directory is now `routes/traditional/proof/lean/`.
See [the migration map](MIGRATION.md) for previous paths.

```text
routes/
  traditional/   # Claude: explicit estimates, papers, code, certificates, Lean
  qrh/           # Codex: QRH(7/8), papers, code, certificates, Lean
AUTHORS.md
RESEARCH_PROTOCOL.md
AGENTS.md
```


| Location | Contents | License scope |
|---|---|---|
| `routes/traditional/proof/` | Current traditional review package: manuscript, certificates, code, Lean, input audits, and conversation | [Apache-2.0](LICENSE) |
| `routes/traditional/review/`, `routes/traditional/SOURCES.md`, `routes/traditional/ROADMAP.md`, `routes/traditional/LOG.md` | Traditional reviews, sources, research plan, and historical log | [Apache-2.0](LICENSE) |
| `routes/traditional/code/`, `routes/traditional/docs/`, `routes/traditional/results/` | Earlier traditional working files, including superseded constants and withdrawn settings; the current claims are in `routes/traditional/proof/` | [Apache-2.0](LICENSE) |
| `routes/qrh/` | QRH-track paper, certificates, code, Lean, scope statements, audit records, and release hashes | Original code: **0BSD**; original paper, documentation, and data: **CC0-1.0**. See [package license](routes/qrh/LICENSE). |

The root [LICENSE](LICENSE) supplies the default Apache-2.0 terms; the
conditional package states its own license scope. Third-party works and
dependencies retain their original licenses. Cited papers are linked rather
than redistributed.
