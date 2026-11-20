# Historical lower intervals for fourth powers

These nine files reproduce the original 2026-11-06 evidence for every integer \(1\le n\le1{,}904{,}041{,}788{,}883\). Their source is the historical QRH-route workspace `Legendre_k8/`. Each path in the table is relative to both that original directory and this archive. The scripts and proofs use LF. The three historical JSON files use CRLF and are preserved byte for byte.

| Original and archived relative path | SHA-256 of original file |
|---|---|
| [code/certify_lower_range.py](code/certify_lower_range.py) | `e6301fde3f607ea7f6eaea43c6293820c4af0334a1e5ad0c8c0ef71c21343d74` |
| [code/k4_bandlimited_round3.py](code/k4_bandlimited_round3.py) | `924c95379de0cafd32a086372e6ef53f319680952ac0ffd19e8b995b4ecc7f62` |
| [code/k4_selberg_round4.py](code/k4_selberg_round4.py) | `1278dfc72f3b4891e5c537b20dbb878d9f9a8a23443a81a6a0fa0aec83d4468a` |
| [results/lower_range_certificate.json](results/lower_range_certificate.json) | `7ddb2ef9a5c4eaad359e0b5584afca49df2a6d20f6ac6dab4cfecb1b8a2fc410` |
| [results/k4_bandlimited_round3.json](results/k4_bandlimited_round3.json) | `061fb3598c66c6df6dfdac325d519db2b287d904eda92ed6ba32b2dd5f4b37d8` |
| [results/k4_selberg_round4.json](results/k4_selberg_round4.json) | `d365cab11ca44b277764010740b754fe863321ee4ac08233a4fcbeeba8466aa8` |
| [research/LOWER_RANGE.md](research/LOWER_RANGE.md) | `0403fdcbf7c660aa12c4630a2be7002e9b33607e02b3db3fcde94df27ce7c242` |
| [research/K4_BANDLIMITED_ROUND3.md](research/K4_BANDLIMITED_ROUND3.md) | `0f52d2524623af5b6103768f38d4d6ecce2a568e91004f1ee9bed2d098850453` |
| [research/K4_SELBERG_ROUND4.md](research/K4_SELBERG_ROUND4.md) | `17e960bf28b6507dbf6f07cb8da9d37b0b7ae50cb23c71c9c6347818450863a6` |

Run from this `legacy` directory with Python 3.12.10 and python-flint 0.9.0. Two verifiers compare the regenerated JSON object exactly, including the python-flint version, the Arb decimal output and the hashes of their script and proof. All three read local files under this archive and run offline.

~~~powershell
python -B -X utf8 code/certify_lower_range.py --verify
python -B -X utf8 code/k4_bandlimited_round3.py --verify
python -B -X utf8 code/k4_selberg_round4.py --verify
~~~

The first replay checks 44,721 prime witnesses individually with the finite Sorenson–Webster Miller–Rabin bound, then uses nine rows of the corrected Cully-Hugill–Lee Table 2 to reach \(n=767{,}543{,}999{,}996\). The least witness is \(2\) and the largest is \(3{,}999{,}871{,}365{,}034{,}201{,}301\). The other two replays each verify 19 strict interval inequalities and cover \(109.46\le4\log n\le112.5\) and \(112.5\le4\log n\le113.1\), respectively. They use published finite-height RH and zero counting. The next local proof starts at \(113.1\). [Cully-Hugill–Lee, corrected v3](https://arxiv.org/html/2103.05986v3) · [Sorenson–Webster, Theorem 1.1](https://arxiv.org/abs/1509.00864) · [Platt–Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765) · [Next interval](../lower/PROOF.md)

Project attribution is Claude and Codex. Codex leads the QRH route. The three original proof documents retain the historical scope and attribution of these calculations. The repository research protocol assigns 0BSD to original QRH code and CC0-1.0 to original QRH documents and data. The historical notice in `Legendre_k8/proof/LICENSE` expressly covers the conditional k=6 package and records that same division there. The nine original k=4 files contain no file-specific license notice. Third-party references and dependencies retain their own terms. [Project authorship](../../../../../AUTHORS.md) · [Repository research protocol](../../../../../RESEARCH_PROTOCOL.md) · [QRH route license](../../../LICENSE) · [Migration record](../../../../../MIGRATION.md)
