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
| **B. Assuming QRH(7/8)** | Fixed exponent **k = 6** | **Seven named inputs**, including QRH(7/8), CS **arXiv:2507.15184v2** Corollary 1 and its specified rows; [complete statements](routes/qrh/documentation/inputs.md). | [QRH route package](routes/qrh/README.md) · [Chinese paper, PDF](routes/qrh/paper/current/main.pdf) |

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

This route accepts the zeta bound in [OpenAI's official quasi-RH release](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)
as an explicit research premise. [Family 003](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md)
describes the upstream formalization; this project studies its prime-interval consequences.

Under **seven precise inputs** — QRH(7/8), CS v2, Rosser, the integrated explicit
formula, finite-height RH, CHJII and CHL — every integer n≥1 has a prime
`n^6 < p < n^6+6n^5 < (n+1)^6`. The [input register](routes/qrh/documentation/inputs.md)
gives exact statements, source versions and the evidence for each premise.
CS v2 remains a preprint dependency; all seven inputs remain explicit in Lean.

The complete downstream theorem, `sixth_powers_from_named_inputs`, passed a
fresh **241-module** build and its matching proof-dependency audit. Project
analytic intervals and numerical budgets are proved, not additional premises.
See the [exact formalization status](routes/qrh/FORMALIZATION_STATUS.md).

The reorganized package provides a [new twelve-chapter Chinese paper](routes/qrh/paper/current/main.pdf),
[paper-to-Lean guide](routes/qrh/documentation/blueprint/README.md),
[bilingual route entry](routes/qrh/README.md), and a [research-history archive](routes/qrh/research-history/README.md).
The paper explains the actual final trapezoid proof and continuous propagation;
the original polynomial-weight paper and its certificates remain historical.
The old 6% CS-coefficient sensitivity result retains its original scope.

The full-range result is k=6; k=4 and k=3 remain the stage and long-term targets.
The current archival reorganization is [awaiting local review](routes/qrh/REVIEW_THIS_RELEASE.md)
before push. The traditional route's mathematical materials are unchanged by it.

## Read, reproduce, and review

| Purpose | Traditional track | QRH track |
|---|---|---|
| Read the argument | [English manuscript](routes/traditional/proof/manuscript.md) | [Current paper](routes/qrh/paper/current/main.pdf) · [Proof guide](routes/qrh/documentation/blueprint/README.md) |
| Inspect dependencies | [Manuscript §3](routes/traditional/proof/manuscript.md) · [Sources](routes/traditional/SOURCES.md) | [Seven inputs](routes/qrh/documentation/inputs.md) · [BibTeX](routes/qrh/paper/current/references.bib) |
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
