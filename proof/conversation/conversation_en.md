# Conversation record: Legendre's conjecture and primes between consecutive k-th powers (k ≥ 67)

*Automatically converted from the session record exported from the Claude desktop app (`export_to_md.py`). User messages and the assistant's text answers are kept; tool calls are kept only as one-line summaries, and tool outputs and internal reasoning are not kept. The full original record is in the exported zip.*

*English translation of `conversation_zh.md` (AI-assisted translation; the Chinese original is authoritative).*

---

## User (turn 1)

Tell me about Legendre's conjecture

### Assistant

# Legendre's Conjecture

**Statement:** For every positive integer n, there is at least one prime between n² and (n+1)².

The conjecture was proposed by Legendre in the early 19th century. In 1912, at the International Congress of Mathematicians, Landau listed it as one of "Landau's four problems"; the other three are the Goldbach conjecture, the twin prime conjecture, and whether there are infinitely many primes of the form n²+1. None of the four problems has been solved to this day.

## Small examples

| n | Interval (n², (n+1)²) | Primes in it |
|---|---|---|
| 1 | (1, 4) | 2, 3 |
| 2 | (4, 9) | 5, 7 |
| 3 | (9, 16) | 11, 13 |
| 10 | (100, 121) | 101, 103, 107, 109, 113 |

## Why people believe it is true

- **Heuristic estimate:** The interval has length 2n+1. By the prime number theorem, the interval contains roughly n / ln n primes; this number grows as n grows and does not look as if it would suddenly become 0.
- **Numerical verification:** Prime gaps have been computed up to the order of 10¹⁸ and beyond, so the conjecture has been verified for n up to roughly the order of 10⁹.

## Best known results (how far from the goal)

Restating the conjecture: one needs to prove that there is always a prime between x and x + 2√x, i.e. the gap exponent has to reach **1/2**.

| Result | Content |
|---|---|
| Bertrand–Chebyshev (1852) | There is always a prime between n and 2n |
| Ingham (1937) | For n sufficiently large, there is a prime between n³ and (n+1)³ (the "cube version" is already solved) |
| Baker–Harman–Pintz (2001) | For x sufficiently large, [x, x + x^0.525] contains a prime; this is the best exponent at present |
| Chen Jingrun (1975) | There is always a **P₂ number** (a prime, or a product of two primes) between n² and (n+1)² |

**The difficulty:** Even assuming the Riemann hypothesis, one only gets prime gaps of O(√x · log x), one log factor more than the √x that is needed. So the Riemann hypothesis does not imply Legendre's conjecture either.

## Related conjectures (all stronger; if true, they imply Legendre's conjecture)

- **Andrica's conjecture:** √pₙ₊₁ − √pₙ < 1. The derivation is direct: if there were no prime between n² and (n+1)², then the two consecutive primes straddling this interval would have square roots differing by more than 1, contradicting Andrica's conjecture.
- **Oppermann's conjecture:** Each of the two intervals (n²−n, n²) and (n², n²+n) contains a prime.
- **Cramér's conjecture:** Prime gaps are O((log p)²). If true, Legendre's conjecture holds for n sufficiently large.

If you are doing AI4Math-related work, I can write a piece of Python for numerical verification, or give a Lean 4 formal statement of the conjecture.

## User (turn 2)

I'd like to ask you: for the higher-power versions of Legendre's conjecture, have any been proven so far, for example cubes, fourth powers and so on

### Assistant

Yes. **The versions for cubes and higher powers have all been proven for n sufficiently large**. Only squares (the original Legendre conjecture) remain unsolved.

## Known results

| Version | Status | Source |
|---|---|---|
| Squares k=2 | **Unsolved** | — |
| Cubes k=3 | Holds for n sufficiently large | Ingham (1937) |
| Cubes, explicit lower bound | Holds for n ≥ e^(e^33.3) | Dudek (2016) |
| Cubes, improved lower bound | Holds for n ≥ roughly e^(e^32.89) | Cully-Hugill (2023) |
| Cubes, assuming the Riemann hypothesis | **Holds for all n** | Caldwell–Cheng (2005) |
| k-th powers, unconditionally for all n ≥ 1 | First k ≥ 5×10⁹, later improved to k ≥ 1438989, then to **k ≥ 155** | Dudek → Mattner → Cully-Hugill (2023) |

So, to state it precisely:
- **Cubes:** The "n sufficiently large" version has been proven. But the lower bound e^(e^33) is extremely huge, and computer verification cannot possibly reach it. So "holds for all n" is **not yet fully proven** unconditionally; assuming the Riemann hypothesis, it holds.
- **4th powers to 154th powers:** Holds for n sufficiently large; this follows directly from a general result (see the next section). "For all n" likewise still has a middle stretch that is not covered.
- **155th powers and above:** Proven unconditionally for all n ≥ 1.

The specific numbers in the table above were written from memory and have not been checked. If you want to cite them, please consult the original papers.

## Why squares are the dividing line

The interval (nᵏ, (n+1)ᵏ) has length about k·n^(k−1). Writing x = nᵏ, the length is k·x^(1−1/k).

If one can prove "[x, x + x^θ] always contains a prime", then as long as 1 − 1/k > θ, the k-th power version holds for n sufficiently large.

- Ingham's exponent is θ = 5/8 < 2/3, so it suffices to handle cubes.
- The best exponent at present is θ = 0.525 (Baker–Harman–Pintz).
- Squares need θ < 1/2. None of the existing methods can achieve this; the Riemann hypothesis also only gives √x·log x, still one log factor short.

## An interesting application

**Mills' constant** is built precisely on the cube version: there exists a constant A ≈ 1.3064 such that ⌊A^(3ⁿ)⌋ is prime for all n. Mills' (1947) proof relies on "there is always a prime between consecutive cubes" (for n sufficiently large). The numerical value of A was computed under the assumption of the Riemann hypothesis.

## User (turn 3)

That's not what I mean by n sufficiently large; I mean for arbitrary n. n sufficiently large is meaningless

<details><summary>Tool-call summary</summary>

- *[tool call ToolSearch]* select:WebSearch
- *[tool call WebSearch]* primes between consecutive powers n^m (n+1)^m all n smallest m Cully-Hugill
- *[tool call WebSearch]* "prime between" "(n+1)^" "for all n" consecutive kth powers 2025 2026 arXiv improvement exponent 90
- *[tool call ToolSearch]* select:WebFetch
- *[tool call WebFetch]*
- *[tool call WebFetch]*

</details>

### Assistant

Going by your criterion, "holds for all n ≥ 1", **the smallest exponent currently proven unconditionally is k = 86**, from an arXiv preprint of February 2026. **Cubes through 85th powers have not yet been proven unconditionally for all n**. My earlier answer missed this, and the best result I cited then, 155, is already outdated.

## Unconditional results for all n ≥ 1

| Exponent k | Author | Year |
|---|---|---|
| 5×10⁹ | Dudek | 2016 |
| About 1.4×10⁶ | Mattner | 2017 |
| 155 | Cully-Hugill (J. Number Theory) | 2023 |
| 140, later 90 | Cully-Hugill & Johnston | 2023–2025 |
| **86** | Ethan S. Lee (arXiv preprint; no formal publication seen) | 2026 |

Lee's paper also proves a partial result for 70th powers, but it holds only for a subset of n, not for all n.

What these methods actually prove is the stronger form "the interval [x, x + c·x^(1−1/k)] contains a prime for all x", so holding for k usually also means holding for larger exponents.

**Why k is still so large:** The asymptotic methods (Ingham, BHP) give lower bounds of the order of e^(e^33), which computer verification cannot possibly cover. To prove "for all n", one has to combine explicit zero-free regions, the error term of the explicit formula, and numerical verification, and the existing explicit estimates only connect up when k is large.

## Assuming the Riemann hypothesis

- **Cubes, for all n:** Caldwell–Cheng (2005).
- **Going further (2026, arXiv:2602.22502):** For exponent 2+δ (δ ≥ 1/4) and all real x ≥ 1, there is a prime between x^(2+δ) and (x+1)^(2+δ). So under the Riemann hypothesis, all integer powers — cubes, fourth powers, etc. — hold for all n.
- **Squares (Legendre's conjecture itself):** Not proven even assuming the Riemann hypothesis.

Sources:
- [Cully-Hugill, Primes between consecutive powers (arXiv:2107.14468)](https://arxiv.org/abs/2107.14468)
- [J. Number Theory version](https://www.sciencedirect.com/science/article/pii/S0022314X23000112)
- [Cully-Hugill & Johnston, On the error term in the explicit formula of Riemann–von Mangoldt (arXiv:2111.10001)](https://arxiv.org/abs/2111.10001)
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers (arXiv:2602.14340)](https://arxiv.org/abs/2602.14340)
- [Weakening the Legendre Conjecture (arXiv:2602.22502)](https://arxiv.org/abs/2602.22502)

## User (turn 4)

Is there a situation where, in the k-th power setting, the conjecture is guaranteed to hold beyond some definite, sufficiently large value n, so that we only need the computer to compute as close to this value as possible in order to prove the whole conjecture?
My intuition is that the larger k is, the looser this interval is, and the smaller the values we need the computer to compute. Can we find a suitable k such that, relying on the known upper bound and computing a higher lower bound, we make the two meet and thereby prove the statement? Do you understand what I mean?

### Assistant

I understand what you mean, and this is exactly the standard approach today. Results like k = 155, 90 and 86 were proven exactly this way: first use analytic methods to prove "it holds for x ≥ X₀", with X₀ computed as a specific number, then use computation to cover x < X₀; once the two pieces meet, the proof is done. Your intuition is also right: the larger k is, the smaller X₀ is, and the easier it is for the two to meet.

There are, however, two points that differ somewhat from what you have in mind.

## 1. The "computation" part actually has two layers; it is not simply letting the computer search for primes

| Layer | Range covered | Basis |
|---|---|---|
| ① Direct computation | x ≤ 4×10¹⁸ (log x ≈ 43) | Prime gaps have been computed exhaustively up to this range (Oliveira e Silva et al., 2014) |
| ② Explicit short-interval theorems | log x up to several thousand | Rely on computer-verified zeros of the Riemann ζ function (RH verified up to height about 3×10¹², Platt–Trudgian), from which explicit conclusions of the type "[x, x(1+1/Δ)] must contain a prime" are derived |
| ③ Analytic theorems | From log x ≥ some L(k) onward | Explicit zero-free regions, zero-density estimates, and the error term of the explicit formula |

Directly searching for primes (layer ①) can basically only reach 10¹⁹ to 10²⁰; pushing even one more order of magnitude is very expensive. What really does the work is layer ②: the objects being computed are zeros of the ζ function, not primes. For example, in the case k = 140, layer ③ holds from log x ≥ 4242, and layer ② can cover up to log x ≈ 4367; the two just overlap, and the proof is complete.

## 2. For small k, the gap between the two pieces is not something "computing a bit longer" can fill

Take cubes as an example. The known analytic lower bound is n ≥ e^(e^32.892):

- Converted to x = n³, this is about log x ≈ 6×10¹⁴, i.e. x has about 2.5×10¹⁴ digits.
- What computation can cover is log x up to several thousand.

The two still differ by a factor of about 10¹¹ on the logarithmic scale. Primes have to be confirmed interval by interval, and the number of intervals below x is itself astronomical, so no matter how fast the computer is, it cannot possibly get through them exhaustively.

## Why X₀ grows so terrifyingly as k gets smaller

The interval (nᵏ, (n+1)ᵏ) has length about k·x^(1−1/k). Analytic methods can guarantee "an interval of length x^θ contains a prime", and two factors are involved here:

1. **The margin (1−1/k) − θ:** For k = 3, the margin is 2/3 minus Ingham's 5/8, leaving only 1/24. BHP's 0.525 is better, but it uses sieve methods, which are almost impossible to make explicit with constants. With such a small margin, the constants in all the error terms are amplified into a doubly exponential X₀. When k is large, 1−1/k is close to 1, the margin is wide, and even crude explicit estimates are good enough.
2. **The quality of the explicit constants:** The explicit versions of zero-free regions and zero-density estimates all have poor constants. Lee's 2026 paper quantifies exactly this: for each k ≥ 65, how large the zero-free region must be, at minimum, for the two pieces to meet. This amounts to computing precisely "how far there is still to go".

## Conclusion

- **Your idea is the current method.** There are three levers driving it: verifying more ζ zeros (extending layer ② upward), improving the explicit zero-free region and zero-density constants (pushing layer ③ downward), and joining up the middle stretch more finely. All three are advancing, which is why k has come down from 155 to 86.
- **But this road can hardly go all the way down to k = 3.** For cubes the gap is doubly exponential; it requires a theoretical breakthrough, for example a very strong explicit version of zero-density estimates. Computing power alone is not enough.
- **For k = 2 this road does not work at all.** The square case has no "holds for x sufficiently large" piece: analytic methods cannot prove it at all, even the Riemann hypothesis is not enough, so there is no analytic lower bound to meet.

## User (turn 5)

What about larger k, then? For example fourth powers, or higher?

<details><summary>Tool-call summary</summary>

- *[tool call WebFetch]*
- *[tool call WebFetch]*
- *[tool call WebSearch]* Ethan Lee "consecutive perfect kth powers" zero-free region 86th powers 70th powers Legendre milestones

</details>

### Assistant

Fourth powers have **not yet** been proven for all n either. The current situation can be split into three ranges of k:

| k | For n sufficiently large | For all n ≥ 1 (unconditional) | For all n (assuming the Riemann hypothesis) |
|---|---|---|---|
| 2 | Not proven | Not proven | Not proven |
| 3 to 85 | ✅ Proven (since Ingham 1937) | ❌ **Not proven** | ✅ |
| **86 and above** | ✅ | ✅ **Proven** (Lee 2026) | ✅ |

- **Why "86 and above" covers all larger k at once:** These papers actually prove a stronger interval form: "for all x ≥ 1, [x, x + c·x^(1−1/k)] contains a prime". For x ≥ 1, the exponent 1−1/k′ increases with k′, so the interval corresponding to a larger k′ can only be longer. So holding for 86 automatically means holding for all larger exponents, with no need to verify them one by one.
- **70th powers:** Lee proved it only for a subset of n (a certain specific integer sequence), not yet for all n.
- **The specific gap for 4th to 85th powers:** I did not find publicly available explicit values of X₀ for small exponents like k = 4. Lee's paper only computes "how large the zero-free region must be for the two to meet" for k ≥ 65, which suggests that smaller k are currently even farther away, and no one has even done a quantitative analysis yet. The fourth-power case is better than cubes (the margin is 3/4 − 5/8 = 1/8, whereas cubes only have 1/24), but my estimate is that it is still a gap of doubly exponential order.

I was not able to open the full text of Lee's paper; what I said about it above comes from abstract-level information. According to ResearchGate's record, the paper will be published in Acta Arithmetica (October 2026).

Sources:
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers (arXiv:2602.14340)](https://arxiv.org/abs/2602.14340)
- [Ethan S. Lee homepage](https://sites.google.com/view/ethansleemath/home)
- [ResearchGate entry](https://www.researchgate.net/publication/377361334_Explicit_zero-free_regions_for_the_Riemann_zeta-function)
- [Cully-Hugill & Johnston (arXiv:2111.10001)](https://arxiv.org/abs/2111.10001)
- [Cully-Hugill, Primes between consecutive powers (arXiv:2107.14468)](https://arxiv.org/abs/2107.14468)

## User (turn 6)

With this route I'm thinking of, where the upper and lower bounds approach each other, roughly how far down in k do you think it can get at most? You have to read the papers; you can't just guess blindly

<details><summary>Tool-call summary</summary>

- *[tool call update_plan]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Read]* C:\Users\BERNKA~1\AppData\Local\Temp\claude\b655f75746a6057d\90b3c2a2-c8b4-40d3-ab12-83d1bb5bc915\scratchpad\papers\2602.14340.txt

</details>

### Assistant

I have finished reading Lee's paper, and the information in it is key. Now let me look at what a few other papers say about the limit.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call wrap_up]*

</details>

## User (turn 7)

You need to consider two points: first, whether the ideas of earlier work can be optimised to knock this upper bound down; second, think about whether there is a better algorithm to push the computational lower bound up

*(message sent by the user while the assistant was working)*

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*

</details>

### Assistant

Going by the data in these papers, this "upper and lower bounds meeting" route **currently reaches k = 86**. With limited improvements to the zero-free region, it can **optimistically be pushed to k ≈ 67–70**. **k ≤ 10 is structurally out of reach within the existing framework, and the paper's authors directly call cubes "futile"**.

I checked both directions you raised against the papers. The conclusion: **the gap can almost only be filled from the analytic side (the "upper bound"); the computational side (the "lower bound") can hardly contribute anything substantial.**

## I. Where the two lines stand now (Tables 3 / 5 of Lee 2026)

| k | Starting point log x of the analytic method | log x covered by computation | Result |
|---|---|---|---|
| 90 | 1997 | 2767 | ✅ Meet |
| **86** | **2010** | **2640** | ✅ Meet (Lee's theorem) |
| 85 | 5587 | 2609 | ❌ |
| 75 | 5880 | 2292 | ❌ |
| 70 | 15951 | 2135 | ❌ |
| 67 | 238050 | 2040 | ❌ |
| 65 | 4.1×10⁷ | 1977 | ❌ |

- **The upper limit of what computation covers** is almost a linear function of k. From Lee's Prop. 3.3 I derived that it satisfies log x ≲ k·(log k + log Δ), where Δ = 2.52×10¹¹ (the explicit interval estimate of Cully-Hugill–Lee). Computing with this formula gives 2640 for k = 86 and 2135 for k = 70, consistent with the numbers in the table.
- **The analytic starting point** suddenly jumps up for k ≤ 85. The reason is a technical condition in the paper: the parameter must satisfy θ > 1/k. For k ≥ 86 a better set of constants (1/85, 12.782) can be used; for k ≤ 85 they can no longer be used. As k goes further down, the starting point keeps getting worse.

## II. Direction 1: improve earlier methods to push the analytic starting point down

Lee breaks the method into three components and assesses the room for improvement of each:

1. **The error term of the explicit formula:** The gist of Lee's own words is "existing results are already quite sharp; only small touch-ups to the constants remain". **There is very little room here.**
2. **The zero-free region:** **This is the main lever.** The zero-free region has the form σ ≥ 1 − log log t /(Z log t); the smaller the constant Z, the larger the region. What has been proven so far is Z = 19.62 (Yang 2025). Lee's Theorem 1.4 computes the Z needed for each k, and **it only needs to hold up to a finite height**:

   | k | Need Z ≤ | Need only hold for heights t ≤ … |
   |---|---|---|
   | 85 | 17.27 | e^75.9 |
   | 70 | 14.06 | e^264 |
   | 67 | 13.41 | e^4121 |
   | 66 | 13.20 | **e^691820** |

   Between 67 and 66 there is a cliff; this is the basis for my saying "the limit is about 67". Lee regards the requirement for k = 70 as "seemingly reasonable", an important milestone.

   My own judgment: e^264 is far beyond what direct numerical verification of zeros can reach (the Riemann hypothesis has currently only been verified up to height 3×10¹² ≈ e^28.7). So this step has to rely on theory — that is, better explicit upper bounds for the ζ function at moderate heights, leading to better zero-free region constants — rather than on computation.

3. **The zero-density estimate N(σ, T):** Lee used the technique of "combining several density estimates" and improved the results for 67 ≤ k ≤ 85. He points out explicitly that if stronger explicit density estimates of a suitable shape could be proven in the range T ≤ e^80, one could push further down.

**There are also two structural walls:**

- **k ≤ 10:** The truncated explicit formula they use requires T < x^(1/10), while θ > 1/k is also needed, so for k ≤ 10 the parameters simply cannot be set within this framework. To break through, one would have to enlarge the range of validity of the explicit formula. Cully-Hugill–Johnston point out that in theory this range can be enlarged at most to 1/2.
- **Cubes:** Johnston et al. (2026) say explicitly that making Ingham's argument explicit "appears futile". To do cubes one needs different tools: explicit versions of **Harman's prime-detecting sieve** or of **Iwaniec's linear sieve (with well-factorable remainder)**. They point out that neither exists in the literature. This is the part of "improving earlier ideas" that genuinely requires originality.

## III. Direction 2: use better algorithms to push computational coverage up

**The direct prime-search road:** The best current algorithm is the method of Sorenson–Webster, which Johnston et al. extended to cubes. It relies on BLS primality proofs, sieving in arithmetic progressions, and batching many intervals together. Under the Cramér model, verifying up to n ≤ N takes O(N log N log log N) time, which is already close to linear, because every interval has to yield at least one prime certificate. The algorithm requires an exponent α > 3/2, so it cannot be used for squares or below. Cubes have been done up to n ≤ 2.55×10¹³, at a cost of about 415,000 core-hours.

**Why using it to fill the k-th-power gap does not help (the following is my own calculation):** Verifying up to n ≤ N only covers up to log x = k·log N. To meet the analytic starting point, one needs N = exp(starting point/k):
- k = 85: N ≈ e^65.7 ≈ 3×10²⁸, which is 10¹⁵ times current capability.
- k = 70: N ≈ e^228 ≈ 10⁹⁹.

Moreover, the larger k is, the more digits the numbers in each interval have, and the more expensive a single primality proof becomes.

**The road via analytic interval estimates (increasing Δ):** The coverage upper limit is k·(log k + log Δ), and Δ enters only logarithmically. For k = 85 to meet, one would need log Δ ≈ 61, i.e. Δ ≈ 10²⁶, whereas it is 2.5×10¹¹ now. My guess is that Δ is limited by the height up to which the Riemann hypothesis has been verified; the paper does not say this directly. If so, one would need to verify the Riemann hypothesis up to a height of order about 10²⁶, which is unrealistic.

**Comparison with cubes:** Computation has reached log n ≈ 31, while the analytic starting point is at log n ≈ e^32.5 ≈ 1.3×10¹⁴; the gap is a factor of more than 10¹², and that is a gap on the logarithmic scale.

## Conclusion

The two sides grow at asymmetric rates: the coverage on the computational side grows only linearly in k, and depends only logarithmically on computing power and on Δ; the analytic starting point, on the other hand, blows up sharply as k decreases. So the meeting point is determined almost entirely by the analytic side.

My estimate:
- Optimising existing ideas (mainly zero-free regions and zero-density estimates at moderate heights) can get to about **k ≈ 70, at most around 67**.
- k ≤ 10 needs a new explicit formula.
- Cubes need a new tool: **explicit sieves**.
- Squares cannot be done even assuming the Riemann hypothesis.

Sources:
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers (arXiv:2602.14340)](https://arxiv.org/abs/2602.14340)
- [Johnston, Sorenson, Thomas, Webster, Primes and almost primes between cubes (arXiv:2601.15564)](https://arxiv.org/abs/2601.15564)
- [Visser, Effective short intervals containing primes (arXiv:2508.18786)](https://arxiv.org/abs/2508.18786)
- [Cully-Hugill & Johnston, On the error term in the explicit formula of Riemann–von Mangoldt (arXiv:2111.10001)](https://arxiv.org/abs/2111.10001)
- [Cully-Hugill, Primes between consecutive powers (arXiv:2107.14468)](https://arxiv.org/abs/2107.14468)

## User (turn 8)

So do you think the idea of "finding solutions level by level as k gradually decreases", eventually approaching cubes or even squares, is right? Or should one work directly on the square or cube problem

### Assistant

I think this idea is **not right**. Going down k level by level will not reach cubes, let alone squares. The reason is that the obstacles met along the way **change in kind**, not just in difficulty: each wall requires a new tool, and the techniques that conquer large k are of almost no help against the next wall.

## Why "level-by-level descent" does not work

| Range | Where it gets stuck | What is needed |
|---|---|---|
| 86 → about 67 | Explicit constants of zero-free regions and zero-density estimates | Optimisation of constants, an "engineering" kind of improvement |
| Around 66 | The required height of the zero-free region jumps from e^4121 to e^691820, a cliff | The shape of the zero estimates has to improve, not just the constants |
| ≤ 10 | The truncated explicit formula is only valid for T < x^(1/10); the parameters have no solution | A new explicit formula (the theoretical limit is x^(1/2)) |
| 3 (cubes) | The ζ-function route is called "futile" by the authors | **An explicit Harman sieve or Iwaniec linear sieve**, neither of which exists in the literature yet |
| 2 (squares) | Even the Riemann hypothesis is not enough; one log factor short | A theory of prime gaps that goes beyond the Riemann hypothesis |

In addition, the progress in k is itself converging: 155 → 140 → 90 → 86, all achieved by refining constants, with each step advancing less than the one before. Proving k = 70 would not directly help with k = 69 either; the only things that carry over are the improved "components".

## A better approach: choose problems by "tool" or "bottleneck", not by k

**1. Do cubes: attack the real bottleneck directly.**
- The core is to make Harman's sieve (or the Baker–Harman–Pintz family of prime-detecting sieves) explicit. This is very hard, but it is the only road to cubes that has been named; the 2026 paper of Johnston et al. says explicitly that it is needed.
- Supporting work on the computational side: cubes have already been verified up to n ≤ 2.55×10¹³. Once the starting point given by an explicit sieve falls within computable range, the two sides can meet.

**2. Approaching squares: switch ladders and go down in Ω (the number of prime factors).**
- Known results: between squares there is always a number with Ω ≤ 4, for all n (Dudek–Johnston); between cubes there is always a number with Ω ≤ 2, for all n (Johnston et al., 2026); Chen Jingrun proved that for n sufficiently large there is a P₂ number between squares.
- So "Ω ≤ 3 between squares, then Ω ≤ 2, for all n" is a ladder that points directly at Legendre's conjecture and is actionable.
- But this ladder stops at Ω = 2: this is the **parity barrier** of sieve methods (Selberg) — pure sieve methods cannot distinguish primes from cases other than Ω = 1. To get past it, one again has to go back to Harman-type methods that bring in bilinear forms.

**3. The conditional route: go down in real exponents.**
- Assuming the Riemann hypothesis, it is already known that the exponent 2 + δ (δ ≥ 1/4) holds for all x (arXiv:2602.22502). Pushing δ toward 0 and giving explicit results is a clear conditional ladder.

**4. Working directly on squares:** I do not recommend taking it on as a project unless the goal is breakthrough-level work. It is stronger than the Riemann hypothesis, and there is currently no known route.

## Recommendations

- **If you want publishable, concrete progress:** Work on targets of the k ≈ 70 type. Lee has already computed the zero-free region constants that are needed, so the target is very clear. Work of this kind takes the form of explicit inequalities, parameter searches and extensive verification, which is well suited to automation with AI or Lean. But be clear that it will not lead to cubes.
- **If you want to genuinely get closer to Legendre's conjecture:** Work on "explicit sieves" (as preparation for cubes), or on the "Ω ladder between squares". These two are the roads that point directly at the goal.

## User (turn 9)

OK. Then leave a research roadmap and a log under the local path, and try to crack the Legendre conjecture for k=67

### Assistant

First I'll set up the research directory, then reproduce Lee's computational framework, and then look within that framework for improvements that can close the k=67 gap.

<details><summary>Tool-call summary</summary>

- *[tool call update_plan]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Read]* D:\UGit\AI4Math\legendre_k67\code\lee_code\code.py
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\LOG.md
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\code\bound.py
- *[tool call Bash]*

</details>

### Assistant

Reproduction succeeded: at the c values given by Lee, δ crosses 1 exactly at the thresholds he reports. Fixing an overflow problem and continuing.

<details><summary>Tool-call summary</summary>

- *[tool call Edit]* D:\UGit\AI4Math\legendre_k67\code\bound.py
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

While the background computation runs, I'll write the results so far into the log.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\ROADMAP.md
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call wrap_up]*

</details>

### Assistant

**k=67 has not been cracked yet.** I narrowed the gap from 2041 < L < 238050 down to 2041 < L < about 7000 (L = log x), and reduced the remaining gap precisely to a specific problem about the distribution of zeros. All numbers come from floating-point computations and have not yet been made rigorous with interval arithmetic.

## Progress made

**1. Reproduced Lee's results.** With my rewritten program and Lee's parameters plugged in, the quantity crosses 1 at the thresholds he reports for k = 67, 70, 85, 86 and 90.

**2. Found an improvement with a large effect.**
- While reading Lee's code I found that his two zero-density estimates (KLN and Bellotti) are used separately.
- When the Bellotti version is used, zeros with β < 0.985 can only be estimated trivially, and this term locks the parameters in place.
- I used the two estimates piecewise within the same integral: KLN for the part where σ is smaller, Bellotti for the part where σ is close to 1. Both are upper bounds for the same quantity, so using them piecewise is legitimate.

| k | Upper limit of the lower segment (computational side) | Lee's analytic starting point | Improved analytic starting point |
|---|---|---|---|
| 70 | 2135 | 15 951 | 5950 |
| **67** | **2041** | **238 050** | **about 7000** |
| 65 | 1978 | 41 432 145 | 7900 |

For k ≤ 72 the improvement is 1 to 4 orders of magnitude, but no k < 86 closes as a result.

**3. Diagnosed the remaining gap precisely.** The bottleneck is information about the distribution of zeros of the ζ function at heights from e^29 to e^110.

## The two levers you raised

**Pushing the computational side up:** To close the gap, one would need to verify the Riemann hypothesis up to about 10^45.6, whereas it currently only reaches 10^12.5. This road does not work.

**Pushing the analytic side down:** There are three concrete targets; achieving any one of them would close the gap.
- **A smoothed explicit formula:** In an idealised model, the gap shrinks to 2041 < L < about 5300.
- **A zero-free region at moderate heights:** Given smoothing, one would only need to improve the Littlewood constant from 19.62 to about 16.5 at heights e^30–e^75, a difference of about 16%. Lee's original requirement was the constant 13.4, with heights up to e^4121.
- **A log-free zero-density estimate at moderate heights:** It would need a constant C of about 1.7×10⁴; Bellotti's existing one is 3.7×10⁵, about 22 times too large.

## Files

- [ROADMAP.md](ROADMAP.md): research roadmap, including quantitative targets for routes A–D and a list of next steps
- [LOG.md](LOG.md): research log
- [code/bound.py](code/bound.py): core of the upper-bound computation, with three modes; the other scripts are all under `code/`
- [results/](results/): scan data
- `papers/`: PDFs and extracted text of 6 papers
- `code/lee_code/`: Lee's original code

`code/req_density.py` is a buggy early version and has been superseded by `code/req_density2.py`.

If the hybrid improvement itself is made rigorous, it would improve Table 3 and Theorem 1.4 of Lee's paper, and could be written up separately as a short paper.

## User (turn 10)

Make it rigorous first and archive it, then continue researching smoothing

### Assistant

Rigorisation first. I am rewriting the upper bound in arb ball arithmetic, covering L with continuous intervals (not just grid points), and checking the hypotheses of the propositions one by one.

<details><summary>Tool-call summary</summary>

- *[tool call update_plan]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\code\rigorous_hyb.py
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The rigorous version agrees with the floating-point results; the upper bound over a whole segment is only slightly larger than the single-point value. Now doing a complete covering for k=67, going down from L=238050.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

All 21 values of k passed rigorous verification. Next I'll re-check all the certificates with the checker: recompute the upper bound segment by segment, and confirm that consecutive segments join end to end with no gaps.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The conditional certificates all passed the re-check, but the maximum δ for every k is only about 0.29, which means the z found by the binary search is not being limited by δ. Some hypothesis may be silently binding; let me check.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Read]* D:\UGit\AI4Math\legendre_k67\code\rigorous_hyb.py
- *[tool call Edit]* D:\UGit\AI4Math\legendre_k67\code\rigorous_hyb.py
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The low-height pass had no effect; the results did not change. Let me look directly at what happens at the top of the k=85 window.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

## User (turn 11)

Is arb really that hard to install? Can I help you?

<details><summary>Tool-call summary</summary>

- *[tool call update_plan]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\docs\HYB_theorem.md

</details>

### Assistant

The theorem document is written; the two entries for k=75 and 67 in Theorem B will be filled in once the background computation finishes. While waiting, I'm starting on smoothing: first the derivation and a floating-point implementation.

<details><summary>Tool-call summary</summary>

- *[tool call update_plan]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\code\smooth.py
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\docs\smoothing.md
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\code\rigorous_smooth.py
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The expressions in `rigorous_hyb` all divide the numerator of a Fraction by that same Fraction's denominator, which is correct, so Theorems A and B are unaffected. Re-testing the rigorous smoothing:

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call WebSearch]* Bellotti "explicit log-free zero density estimate" Riemann zeta arXiv
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The rigorous covering got stuck when it reached L = 3191.31, where δ exactly touches 1. The earlier floating-point sampling had skipped over this point. Doing a fine scan nearby:

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

One spot in the coverage check is not rigorous enough: when deciding whether the left endpoint of a cell is covered, one should use the **upper** endpoint of the row lower bound T0, not its lower endpoint. Fixing this and rerunning.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Read]* D:\UGit\AI4Math\legendre_k67\papers\2405.12545.pdf

</details>

### Assistant

There is no PDF rendering tool, so I'm re-reading Table 2 with a second, independent extraction method (pypdf) and comparing it item by item with the numbers I entered.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The HTML version is generated from the LaTeX source, and the values in it agree exactly with the ones I entered. Now comparing item by item once more with a program, and looking at the results of the certificate re-check:

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*

</details>

### Assistant

All 22 rows agree. The certificate re-check has not finished in the background yet, so I'm rerunning it in the foreground instead:

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call WebSearch]* Andrew Yang thesis "explicit zero-free regions for the Riemann zeta-function" UNSW 2025 4.862 19.62
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\docs\k67_theorem.md
- *[tool call Edit]* D:\UGit\AI4Math\legendre_k67\docs\HYB_theorem.md
- *[tool call Edit]* D:\UGit\AI4Math\legendre_k67\docs\HYB_theorem.md
- *[tool call Edit]* D:\UGit\AI4Math\legendre_k67\docs\smoothing.md
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\ROADMAP.md
- *[tool call Bash]*

</details>

### Assistant

Wrapping up: recording memory and giving a summary.

<details><summary>Tool-call summary</summary>

- *[tool call Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\research-grounded-in-papers.md
- *[tool call Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\legendre-k67-project.md
- *[tool call Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\MEMORY.md
- *[tool call wrap_up]*

</details>

### Assistant

**The k=67 gap is closed:** I obtained a computer-assisted proof that **for all k ≥ 67 and all n ≥ 1, (n^k, (n+1)^k) contains a prime**. The best previously known result was k ≥ 86 (Lee 2026). All certificates were rigorously verified with arb ball arithmetic and re-checked, but this conclusion has not yet been reviewed by a human, and it depends on the Littlewood constant 19.62 from Yang's PhD thesis. Lee's k=86 theorem also depends on it. Using only the formally published constant 21.233, the gap does not close.

Also, to answer the question you asked midway: arb installed with a single `pip install`; no help was needed. What was slow is some of the computations themselves.

## 1. Rigorisation and archiving (HYB method)
- The method that hybridises the two zero-density estimates, KLN and Bellotti, has been rigorously verified with ball arithmetic by covering continuous L intervals, producing 21 certificates (k = 65…85), all of which passed independent re-checking.
- Rigorous thresholds: the analytic starting point for k=67 drops from Lee's 238050 to 6989.94, and for k=65 and 66 from about 4×10⁷ to about 8000.
- Improved Lee's Theorem 1.4 (conditional zero-free region). For k=67 the zero height required drops from e^4121 to e^108.8, while the required constant stays essentially unchanged.

## 2. Smoothing research
- Replaced the sharp cutoff with a smooth weight, derived an explicit upper bound, and then made a rigorous version of it.
- Using only the part of Bellotti's table that Lee cites, the k=67 gap shrinks to (2343.8, 5535.3), which still does not close.
- **Key finding:** Bellotti's density-estimate table actually starts at height 3×10¹², but Lee cited only the rows above e^80. These 22 low-height rows are of no use within Lee's framework, but they become usable in combination with the hybrid method. I checked the values in these 22 rows item by item against two independent sources.
- With the three things combined (hybrid + smoothing + full table), the whole k=67 gap is covered by 1241 segment certificates, with maximum δ = 0.937.
- k=66 and 65 cannot be closed with this method, so under the current inputs 67 is exactly the limit of the method.

## 3. Bugs found and fixed
Several bugs were found during development. All have been fixed, and all affected results have been recomputed and re-checked:
- The conditional version, in KLN mode, omitted one segment of the zero integral (the earlier conditional results were invalidated and recomputed);
- Mismatched numerator and denominator in a fraction conversion;
- The tail truncation point was chosen too small;
- Cells straddling a boundary of Bellotti's table fell back to a very large upper bound.

## 4. Items still awaiting review
See `docs/k67_theorem.md` §6 for details:
- The constant 19.62 has not yet been formally published;
- The smoothed explicit formula needs a formal citation or a complete proof;
- Lee's Prop 3.2 and 3.3 are cited directly and have not been redone rigorously;
- Ideally, someone should independently recompute the certificates with a separate implementation.

## Files
- [docs/k67_theorem.md](docs/k67_theorem.md): main theorem, proof structure, list of inputs, re-checking method
- [docs/HYB_theorem.md](docs/HYB_theorem.md), [docs/smoothing.md](docs/smoothing.md): the two new propositions and their proofs
- [ROADMAP.md](ROADMAP.md), [LOG.md](LOG.md): roadmap and research log
- `results/`: certificates; the re-checking commands are given in the main theorem document

Sources:
- [Lee, arXiv:2602.14340](https://arxiv.org/abs/2602.14340)
- [Bellotti, arXiv:2405.12545](https://arxiv.org/abs/2405.12545)
- [Bellotti–Trudgian–Yang, arXiv:2603.21490](https://arxiv.org/abs/2603.21490)
- [Mossinghoff–Trudgian–Yang, arXiv:2212.06867](https://arxiv.org/abs/2212.06867)
- [Yang, arXiv:2301.03165](https://ar5iv.labs.arxiv.org/html/2301.03165)
- [Cully-Hugill–Johnston, arXiv:2111.10001](https://arxiv.org/abs/2111.10001)
- [Visser, arXiv:2508.18786](https://arxiv.org/abs/2508.18786)
- [Johnston et al., arXiv:2601.15564](https://arxiv.org/abs/2601.15564)

## User (turn 12)

You... really proved it?

### Assistant

It cannot be put that way. The accurate statement is: I have obtained a **candidate proof**. The chain of reasoning is complete, and the numerical part has been rigorously verified, but it is still several hurdles away from a "proof" the mathematical community would accept. Until those hurdles are cleared, no one should claim publicly that "67 is proved".

## What has been done
- **The proof chain is complete:** Four ranges join exactly end to end, covering all x ≥ 4×10¹⁸. The two middle segments are covered by my certificates; the two ends cite Lee's propositions.
- **The numerical part is rigorous:** It uses arb ball arithmetic and covers continuous intervals of L rather than sampling grid points. All certificates were recomputed by an independent re-checker.
- **There are several consistency checks:** The program reproduces all of Lee's thresholds digit for digit; the rigorous and floating-point values agree with each other; the improvement has a clear source, mainly the low-height rows of Bellotti's table that Lee did not use.

## Where it could be wrong (from highest to lowest risk)
1. **My own two new propositions (the hybrid density estimate and the smoothed upper bound) have only been checked by me.** Every step looks like a standard argument, but no number theory expert has reviewed them yet.
2. **The code may still contain bugs.** In this round alone I found and fixed 4. One of them at one point invalidated all the results of the conditional version. This shows that the probability of error is not low.
3. **Some input constants were taken second-hand from Lee's paper.** KLN's 17.253 and 5.663, the explicit formula's 1.26, and the bound for ψ−θ: I did not go back to the original papers to check each of them. Only Bellotti's table was checked by me against the original.
4. **The conclusion depends on a constant that has not been formally published.** The 19.62 in Yang's PhD thesis has only been cited by the author themself, in a 2026 arXiv paper. If it is replaced by the published 21.233, the gap does not close.
5. **Lee's Prop 3.2 and 3.3 are cited directly.** His own code only checks at the threshold points, and has a bug in its precision setting.

## What is still needed to make it a real proof
- Have someone who works in explicit analytic number theory review the two propositions in `docs/k67_theorem.md`;
- Check every input constant against the original paper;
- Independently recompute the certificates with a separate implementation;
- Run several known-answer tests. For example, use the same machinery to re-derive the constant Δ in the Cully-Hugill–Lee interval estimate: if the result comes out absurdly better, something is wrong;
- Wait for 19.62 to be formally published, or confirm it with the author.

My own judgment: this result **is quite likely correct**. The idea holds up, because both techniques are standard methods, and Lee's framework happens to be unable to use those low-height table rows. But "quite likely" is still a long way from "proven". I suggest completing the items above before considering writing it up as a paper or contacting authors such as Lee and Bellotti.

## User (turn 13)

Here's what to do: first write up your results as a document that is easy for humans to review, with every condition clearly marked and the references and citations clearly marked; then go through a Lean formal proof; and archive all of this in a "proof" subfolder. I want other mathematical experts and other reviewing AIs to review this result.

### Assistant

I'll do this in three parts:
1. A manuscript that is easy to review: every premise numbered and marked with its source and verification status, with full citations.
2. Lean formalisation.
3. Archive the certificates, the code and a one-click re-checking script together in the `proof/` folder.

First, let me check whether Lean and TeX are installed on this machine.

<details><summary>Tool-call summary</summary>

- *[tool call update_plan]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

Lean 4.35.0 is installed. Next I'll set up a Lake project that depends on Mathlib, and download Mathlib's precompiled cache in the background.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Agent]* Verify density/counting inputs
- *[tool call Agent]* Verify explicit-formula inputs
- *[tool call Agent]* Verify zero-free regions, Lee Prop 3.2

</details>

### Assistant

The three checking agents are now running in the background. Starting the Lean part: first confirm that the template project compiles, then see whether Mathlib already has a Chebyshev θ function and a summation-by-parts lemma that can be used.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\LegendreK67\LegendreK67\Reduction.lean
- *[tool call Bash]*

</details>

### Assistant

The reduction part compiled on the first try, with only one harmless linter warning. Next: θ ⇒ prime, the interval assembly, Abel summation, and the combination lemma.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The rename failed: the Lean directory is in use, so the copy step after it did not run either. I'll keep the Lean project under its original name `proof/LegendreK67` and copy the files again.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\manuscript.md

</details>

### Assistant

The main body of the manuscript is written. While waiting for the checking reports, I'll write the review checklist and the entry-point README.

<details><summary>Tool-call summary</summary>

- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\REVIEW_CHECKLIST.md

</details>

### Assistant

Checklist item E2 asks "does it prove too much?"; I'll run that test myself first: use the same smoothing code on small k, where it is expected to fail.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The one-click re-check in the archive directory passed in full. Next, fixing the sanity test: for k=3 the upper limit of the lower segment is only L ≈ 82, below the log x ≥ 300 required by (I7), so sampling has to start at 300.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\README.md
- *[tool call Bash]*

</details>

### Assistant

The pure-arb version and the original version differ by about 3×10⁻⁹ (relative error). Numerically this is irrelevant, but it is much larger than the 10⁻¹² safety factor reserved in the original version, so its source has to be tracked down.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

Updating the research log while waiting.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The manuscript, review checklist, Lean formalisation and certificates have all been archived in `proof/`. I am now waiting for the reports of the three literature-checking agents, and for two background re-checks (pure-arb mode, and the one-click re-check with the latest code). When the results come back, I will fill the verification status into §3.1 of the manuscript and then write the final summary.

The first checking report (the explicit-formula part) is back, and one point needs correcting:

- **The T\* question is confirmed to be fine:** CHJ II Corollary 3.3 argues directly about the difference ψ(x+h) − ψ(x), with the same T* used for x and for x+h.
- **Found an error in Lee's paraphrase:** CHJ II actually requires T > max{51, (log x)²}, whereas Lee wrote 2T > max{51, log x}, a much weaker condition. In the range we use, the stronger condition holds with a large margin, but my rigorous checking code followed Lee's weaker condition; it must be changed to the condition in the original, and the certificates then re-checked.
- Other inputs: (3.4) is confirmed via BKLNW; Costa Pereira's original paper could not be accessed, but the lower bound can be derived independently via BKLNW. The 14 pairs (Δ, x₀) of CHL agree with the corrected version. The proof of Lee's Prop 3.3 contains a miswritten inequality, but for k=67 two of the parameter pairs are enough.

Saving the report first, then fixing the code.

<details><summary>Tool-call summary</summary>

- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\input_verification\report_explicit.md
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\input_verification\report_density.md
- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\code\tail.py
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

The earlier change was not written in: either the target string did not match, or the whole command was moved to the background. Looking at the file directly:

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*

</details>

### Assistant

The cause is that the command mistakenly started with a `cat > /dev/null`, which kept waiting on standard input, so none of the later steps ran. First stopping this stuck background task, then re-applying the changes.

<details><summary>Tool-call summary</summary>

- *[tool call ToolSearch]* select:TaskStop
- *[tool call TaskStop]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

Lean compiles, and all theorems still depend only on the three standard axioms. Next, verifying with arb the two numerical facts used in Lean, and looking at the result of the pure-arb re-check.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Bash]*

</details>

### Assistant

`tail.py` and `numeric_facts.py` do not yet return a non-zero exit code when a check fails, so the one-click script would not notice a failure. Adding that, then starting the full re-check.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*

</details>

### Assistant

While the full re-check runs in the background, I'll save the third checking report and then rewrite the manuscript.

<details><summary>Tool-call summary</summary>

- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\input_verification\report_zfr_lee32.md

</details>

### Assistant

First, a quick extra computation: the δ of the smoothing method at a few sample points when only published constants are used, together with the corrected KLN constants. The sensitivity section of the manuscript needs it.

<details><summary>Tool-call summary</summary>

- *[tool call Bash]*
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\manuscript.md

</details>

### Assistant

Manuscript v2 is written. Next, updating the review checklist and the README to match the structure of v2.

<details><summary>Tool-call summary</summary>

- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\REVIEW_CHECKLIST.md
- *[tool call Write]* D:\UGit\AI4Math\legendre_k67\proof\README.md
- *[tool call Bash]*
- *[tool call Bash]*
- *[tool call Edit]* D:\UGit\AI4Math\legendre_k67\ROADMAP.md
- *[tool call Bash]*

</details>

### Assistant

Update the project memory, then wrap up.

<details><summary>Tool-call summary</summary>

- *[tool call Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\legendre-k67-project.md
- *[tool call wrap_up]*

</details>

### Assistant

The review package has been archived in [proof/](proof/README.md) and can be handed to experts and reviewing AIs.

This time I went back to the original literature and checked the inputs one by one, and found 4 problems with the inputs as paraphrased by Lee. After correcting them and recomputing everything, the k=67 argument **still holds**: the one-click re-check in the archive directory reports `ALL CHECKS PASSED`.

## Problems found during checking, and the corrections in v2
1. **The density-estimate constants are unreliable (largest impact).** The KLN constants 17.253/5.663 cited by Lee depend on a bound that has been pointed out to be "unreliable". I switched to the corrected values 17.418/2.231 of Johnston–Yang 2023. These values only cover σ ≥ 0.98, so σ₁ was changed to 0.98, and all certificates were then regenerated.
2. **The condition of validity of the explicit formula was misstated.** The original requires T > max{51, log²x}; Lee wrote a much weaker condition. The code now checks the condition in the original.
3. **One inequality step in the proof of Lee's Prop 3.3 is false.** The lower segment is now derived directly from the Cully-Hugill–Lee interval estimate; this derivation has been formalised in Lean.
4. **Lee's Prop 3.2 gives no monotonicity argument.** I switched to a tail lemma that I proved myself (log x ≥ 10⁸): it uses only published zero-free regions, and its monotonicity condition was verified in arb.

The proof as a whole no longer cites Lee's Prop 3.2 or 3.3.

## Dependencies that must be stated clearly
The conclusion depends on two constants that have **not yet been peer reviewed**:
- **19.62**: Yang's PhD thesis, publicly available;
- **4.896**: Bellotti–Trudgian–Yang, arXiv:2603.21490.

Without either one of them the method does not close; §11 of the manuscript gives the specific data. All other inputs have been formally published and checked against the originals.

## Lean formalisation
- **Proved, with no sorry:** the reduction to all k ≥ 67, the equivalence between a positive increment of θ and the existence of a prime, the derivation of the lower segment, the assembly of the four segments, the Abel summation inequality used in the numerical integration, and the combination step of the two propositions. The axiom audit lists only Lean's three standard axioms.
- **Entering as hypothesis fields, not proved in Lean:** the analytic number theory inputs (zero density, zero-free regions, explicit formula) and the arb numerical certificates. Mathlib does not yet have this part of the theory, so these need human review.

## How to use it
- The entry point is [proof/README.md](proof/README.md); the main manuscript is [proof/manuscript.md](proof/manuscript.md) (in English, for international review).
- The review checklist [proof/REVIEW_CHECKLIST.md](proof/REVIEW_CHECKLIST.md) is ordered by risk and can be sent directly to reviewers.
- How to re-check: run `python verify_all.py` in `proof/code`, which takes about 10 minutes; for the Lean part, run `lake build` in `proof/LegendreK67`.
- When sharing, do not include `LegendreK67/.lake` (about 5 GB); recipients can download it themselves with `lake exe cache get`.

The old results for k ≠ 67 in `docs/HYB_theorem.md` still use the problematic set of KLN constants. They have been marked as needing recomputation, but this does not affect the k=67 review package.

## User (turn 14)

Can you export this main conversation about Legendre's conjecture as an md file, and then write a script or open another window to translate our conversation into English, so that it can be uploaded together?

### Assistant

First I'll export the conversation record, then open a new session to translate it into English.

<details><summary>Tool-call summary</summary>

- *[tool call ToolSearch]* select:mcp__ccd_session_mgmt__export_transcript,mcp__ccd_session__start_session

</details>

