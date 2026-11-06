# Primes between consecutive k-th powers

**English** | [简体中文](README.zh-CN.md)

This repository studies when, for **every integer n >= 1**, the open interval
`(n^k, (n+1)^k)` contains a prime. It contains two research tracks with
different mathematical premises, separate review packages, and separate
verification records.

**Status — 2026-11-06:** public review drafts, produced largely by AI systems.
Neither track has received a recorded complete human expert review, and
neither has an end-to-end Lean formalization of its full analytic argument.

## Results at a glance

Every row below concerns **all positive integers n**, under the stated inputs
and the new arguments in its manuscript.

| Research track | Reported result | Main premises | Review package |
|---|---|---|---|
| **A. Traditional explicit estimates** | Every integer **k >= 70** | The listed explicit estimates, including the **4.896** zero-free-region constant from the Bellotti–Trudgian–Yang preprint. No QRH assumption. | [Traditional manuscript, English](proof/manuscript.md) |
| **A. Traditional, refereed-input variant** | Every integer **k >= 74** | The listed refereed literature inputs, using **5.558691** in place of 4.896. No QRH assumption. | [Traditional review package](proof/README.md) |
| **B. Assuming QRH(7/8)** | Fixed exponent **k = 6** | **H1:** every nontrivial zeta zero has real part at most 7/8. **H2:** CS **arXiv:2507.15184v2**, Corollary 1 and the specified table rows, plus the cited auxiliary inputs. | [Conditional k6 package](conditional-k6/README.md) · [Chinese paper, PDF](conditional-k6/paper/main.pdf) |

“Refereed-input” describes the sources used by that variant; it does not mean
that this project's new proof has been peer-reviewed. The two tracks answer
the question under different premises, so their exponents should be read
with those premises attached.

## Track A — traditional explicit estimates

### Result and method

The [v4 manuscript](proof/manuscript.md) gives computer-assisted arguments for
all integer exponents **k >= 70**, and for **k >= 74** when restricting the
literature inputs to refereed results.

The method combines explicit zero-free regions, hybrid zero-density bounds,
a smoothed explicit formula, finite-range certificates, and an analytic
infinite tail. It does **not** assume QRH(7/8).

The k >= 70 variant uses the preprint constant 4.896. The project's
[AI audit](proof/zfr_audit/bty_4.896/REPORT.md) reports that its proof closes
after specified corrections; this is not human peer review. The k >= 74
variant uses the refereed constant 5.558691. Both variants also use 21.233,
54.004, and the other inputs stated in the manuscript.

### Evidence and limits

Arb certificates cover the numerical ranges. Lean checks the logical assembly
of the ranges **assuming the stated analytic estimates and certificate
conclusions**. It does not prove those analytic estimates or Arb computations.
See the [review checklist](proof/REVIEW_CHECKLIST.md),
[recorded numerical replay](proof/certificates/verify_all_output.txt), and
[Lean scope](proof/README.md#lean-证明了什么).

The input checks and open review tasks remain visible in
[SOURCES.md](SOURCES.md), [input verification](proof/input_verification/), and
[zero-free-region audits](proof/zfr_audit/README.md). In particular, the
Bellotti table was checked against arXiv v2; comparison with the printed
journal table remains a review task.

**The earlier k >= 67 claim was withdrawn.** The project's audit found an
arithmetic problem in the thesis proof of the required constant 19.62.
The finding is the project's reading, not an author-confirmed correction.
See the [audit report](proof/zfr_audit/thesis_19.62/REPORT.md) and
[withdrawn certificates](proof/certificates/withdrawn_k67/README.md).
The historical Lean package name `LegendreK67` is not a current k = 67 claim.

## Track B — assuming QRH(7/8)

### Result and explicit premises

This track accepts QRH(7/8) as a **working hypothesis**; it does not establish
or audit the upstream claimed proof. It also explicitly assumes the
Chourasiya–Simonič **v2** density result, treated as a preprint dependency:
Corollary 1, Table 1 rows indexed **16–27** (the first 12 rows), on their
specified domains. The cited classical auxiliary inputs are listed in the
[paper](conditional-k6/paper/manuscript.md).

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

**46 Lean modules** compile. They include actual Lucas/Pratt proofs of the
1259 prime witnesses, exact range reductions, rational certificate checks,
selected analytic lemmas, and the scalar tail bound. The current assembly
theorem nevertheless has the type

```text
CHLRows -> AnalyticSegmentInputs -> SixthPowerConclusion
```

The three local analytic conclusions in `AnalyticSegmentInputs` have not yet
been derived inside Lean from H1/H2 and the cited inputs. The actual zeta
explicit-formula/density argument and the complete transcendental cell
bounds still need to be connected. See the
[formalization status](conditional-k6/FORMALIZATION_STATUS.md) and
[full theorem types and axiom audit](conditional-k6/audit/kernel_axioms.txt).

The published package passed [Linux numerical and Lean CI](https://github.com/bernkastel299792458/legendre-kth-powers/actions/runs/42153017737)
at commit `58521b6`. This verifies the stated computational and partial
formalization scope, not an end-to-end proof of the conditional theorem.

## Read, reproduce, and review

| Purpose | Traditional track | QRH track |
|---|---|---|
| Read the argument | [English manuscript](proof/manuscript.md) | [Chinese manuscript](conditional-k6/paper/manuscript.md) · [PDF](conditional-k6/paper/main.pdf) |
| Inspect dependencies | [Manuscript §3](proof/manuscript.md) · [Sources](SOURCES.md) | [Paper §1](conditional-k6/paper/manuscript.md) · [BibTeX](conditional-k6/paper/references.bib) |
| Reproduce computations | [Review package](proof/README.md#如何复核) | [Reproduction instructions](conditional-k6/REPRODUCING.md) |
| Understand Lean coverage | [Assembly scope](proof/README.md#lean-证明了什么) | [Completed parts and remaining obligations](conditional-k6/FORMALIZATION_STATUS.md) |
| Review the evidence | [Checklist](proof/REVIEW_CHECKLIST.md) · [AI reviews and responses](review/) | [Scope review](conditional-k6/audit/PUBLICATION_SCOPE_REVIEW.md) · [Historical reviews](conditional-k6/audit/source_reviews/README.md) |

For the **traditional numerical replay**, run from the repository root:

```sh
python -m pip install -r proof/code/requirements.txt
python proof/code/verify_all.py
```

For the **QRH numerical replay**, use **Python 3.12.10** and run from the
repository root. The frozen tail checker includes the Python patch version
in its metadata comparison.

```sh
python -m pip install -r conditional-k6/code/requirements.txt
python conditional-k6/code/release_manifest.py --check
python -X utf8 conditional-k6/code/verify_k6.py --dry-run
python -X utf8 conditional-k6/code/generate_lean_certificates.py --check
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
| **Codex and a separate Claude instance — traditional reviews** | Supplied the AI reviews and associated checks archived under `review/`. |
| **Codex — QRH track** | Developed the conditional argument, refined certificates, Lean components, manuscript, and reproducibility package, with cross-checks in separate agent contexts. |
| **Claude — earlier QRH review** | Reviewed the earlier 76-cell version; its recommendations prompted clearer CS v2 premises and stronger numerical margins. That review does not certify the later Lean implementation. |

AI agreement is not a substitute for mathematical proof or human expert
review. The traditional manuscript contains its detailed contribution
statement and [conversation archive](proof/conversation/); the QRH package
has a separate [AI-use statement](conditional-k6/AI_USE.md). Human author
names, affiliations, and emails remain unfilled in the QRH paper.

## Repository map and licenses

| Location | Contents | License scope |
|---|---|---|
| `proof/` | Current traditional review package: manuscript, certificates, code, Lean, input audits, and conversation | [Apache-2.0](LICENSE) |
| `review/`, `SOURCES.md`, `ROADMAP.md`, `LOG.md` | Traditional reviews, sources, research plan, and historical log | [Apache-2.0](LICENSE) |
| `code/`, `docs/`, `results/` | Earlier traditional working files, including superseded constants and withdrawn settings; the current claims are in `proof/` | [Apache-2.0](LICENSE) |
| `conditional-k6/` | QRH-track paper, certificates, code, Lean, scope statements, audit records, and release hashes | Original code: **0BSD**; original paper, documentation, and data: **CC0-1.0**. See [package license](conditional-k6/LICENSE). |

The root [LICENSE](LICENSE) supplies the default Apache-2.0 terms; the
conditional package states its own license scope. Third-party works and
dependencies retain their original licenses. Cited papers are linked rather
than redistributed.
