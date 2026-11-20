# Pointwise height sums on a rectangle-free compact bridge

The physical range checks of the transfer extend down to \(L=140\). For \(140\le L\le145\), \(d(L)=\log(1+4e^{-L/4})\) gives \(\lfloor\log(.5/d(L))\rfloor\) between 32 and 34, above \(\log H\). The transfer checks \(d(L_0)e^{u_0}<.5\), \(d(L_1)e^{46}>192\), and the three explicit \(e^{u_0}\) edge inequalities at every run. The physical weights, low-ordinate bound, trivial zeros and prime-power errors already apply throughout this range by [the finite-grid proof](IRREGULAR.md). At every slab the boundary routines check their own admissible real exponents and taper endpoints. On \(\log Y<30\) use only the outer Jordan correction with its lower threshold 26. Extending the range of these checks by itself certifies no additional physical cell; each complete budget still has to be strictly below one.

**A pointwise radial bound gives $147.2\le L\le147.81$.** The complete 160-bit certificate on this closed interval is below **.998225**. The lower integer endpoint is $\lceil e^{147.2/4}\rceil=9{,}594{,}822{,}260{,}312{,}770$. Join at $147.8$ to the following closed interval. It uses the same four parameter triples and $(1.1,9.5,-3.25)$ as an additional candidate. The physical mesh is $1/96$, the logarithmic-height mesh is $1/160$, and the old all-height bound takes over at $\log t=46$. At this cutoff $d(147.81)e^{46}>192$, so the exact inverse-square tail formula applies.

For a fixed detector polynomial $P$ with root multiplicity $m$, its radial constant is the supremum over $z$ of $(\log|P(z)|)_+/(m|z|^\nu)$. At $z\ne0$ each positive term is exponential in $\nu$, hence the supremum is log-convex. Given certified positive endpoints $c_0,c_1$ in one row of the [radial table](../../round5/kernel/radial_detectors.py), the value between them is at most $c_0^{1-x}c_1^x$ at relative position $x$. Take the minimum only after interpolation within each row. In logarithmic coordinates a row lying strictly above another at both endpoints can be omitted. The new verifier bounds all unaffected horizontal and right costs exactly as in the $147.8$ bridge.

~~~sh
python -B round6/reduction/exact_bridge.py --modulus 2310 --core 1048576 --alpha 1 --extra-base 210 --smooth centered --interpolate --first 147.2 --last 147.81 --nheight 80 --sub 2 --cells 128 --mesh 96 --top 46 --param "1.16,10,-3;1.04,9.5,-3.5;1.16,9,-3;1.28,9,-3;1.1,9.5,-3.25"
~~~

**With $Q=2310$ the compact bridge reaches $147.8\le L\le149$.** Its normalized cost is below **.985598**, maximized on the cell with left endpoint $147.8$. This connects to the [grouped proof on $L\ge149$](../folds/MODULUS_2310.md) and gives the pointwise fourth-power assertion for every $n\ge11{,}147{,}593{,}054{,}922{,}960$, under the same QRH(7/8) and analytic inputs. The pointwise detector uses $f_{2310}$ on all boundaries, factors its critical-line full function through $\zeta E_{210}$, and controls the short residual with the [partially folded mean](../folds/FOLD_MEAN.md), depth 12 and short core $2^{20}$. On the right it uses $C_{2310}$ throughout and tests both available residue-class bounds up to $100T$ as in the [modulus-2310 bridge](../folds/MODULUS_2310.md). Include 11 in the Euler product in the angular Jensen estimate.

For the critical fourth moment use the [centered phase estimate](../phase/CENTERED_PHASE.md) with scale 1, width .04 and harmonic prefix 384. At each real abscissa and true cumulative ordinate take the minimum of complete bounds for four different $(\delta,W,\log h)$ triples. The physical spacing is $1/48$ and log-height spacing is $1/80$ in half-unit slabs. The same old all-height estimate bounds the integral beyond $\log t=50$, and includes every positive ordinate beyond the finite sum.

~~~sh
python -B round6/reduction/exact_bridge.py --modulus 2310 --core 1048576 --alpha 1 --extra-base 210 --smooth centered --first 147.8 --last 149 --nheight 40 --sub 2 --cells 96 --mesh 48 --param "1.16,10,-3;1.04,9.5,-3.5;1.16,9,-3;1.28,9,-3"
~~~


A finer five-triple replay with the same paired estimate covers **$151.5\le L\le154.6$** with cost below **.982878**. Its integer starting point is $\lceil e^{151.5/4}\rceil=28{,}112{,}761{,}104{,}599{,}138$. Both Q=210 results here use the paired fourth root with the older Minkowski treatment of the small-time range.

~~~sh
python -B round6/reduction/exact_bridge.py --alpha 1.5 --extra-base 210 --smooth shifted --first 151.5 --last 154.6 --nheight 40 --sub 2 --cells 128 --mesh 48
~~~


**The paired fourth moment reaches $L=152$.** With the [phase estimate for the averaged asymmetric cutoff](../phase/SMOOTH_PHASE.md) and the modulus-210 critical factorization, the complete bridge $152\le L\le154.6$ has normalized cost below **.970658**. Combined with the sharp-cutoff bridge below, it gives a prime between consecutive fourth powers for every $n\ge31{,}855{,}931{,}757{,}113{,}757$. This bridge uses three complete detector triples, each with the same right-side modulus 210. On the left the critical mollifier paired with $\zeta E_{210}$ is just $C_{210}$. The short-core subtraction takes folding depth 12 and no residual Euler factors. Use the smaller of the complete original, sharp and paired left norms. For the last one use $\alpha=1.25$, smoothing width .06 and exact harmonic prefix 384. It satisfies the same uniform normalized fourth-moment inequality on every log-height slab. All other estimates in the transfer below are identical.

~~~sh
python -B round6/reduction/exact_bridge.py --alpha 1.5 --extra-base 210 --smooth shifted --first 152 --last 154.6 --nheight 36 --sub 2 --cells 64 --mesh 32 --param ".92,9.5,-3.5;1,9.25,-3.5;1.1,8.75,-3.5"
~~~

The sharp-cutoff modulus-30 variant also certifies **$154.6\le\log x\le155$** with an upper bound below **.993134**. At the included right endpoint use the [independent modulus-30 upper half-line](../folds/BRIDGE.md). Thus sharp cutoffs by themselves give the fourth-power conclusion for $4\log n\ge154.6$. This replay uses the five registered detector triples, height slabs of length $1/2$ with 48 equal steps each, and physical cells of length $1/64$.

~~~sh
python -B round6/reduction/exact_bridge.py --alpha 1.5 --extra-base 30 --first 154.6 --last 155 --nheight 48 --sub 2 --cells 128 --mesh 64
~~~

Assume QRH(7/8), finite-height RH and the analytic inputs of the [previous upper half-line](../../round5/kernel/FINITE_ANCHOR.md). With the [periodic fourth moment for $E_6$](../phase/PERIODIC_FOURTH.md), the entire interval $159.5\le\log x\le162.3$ has a prime $x<p<x+4x^{3/4}$. The verified normalized upper bound is **.987662**. With the [additional modulus-30 critical mean](../folds/FOLD_MEAN.md) the complete interval $156.5\le\log x\le162.3$ similarly has bound **.959255**. No finite-box zero-count conjecture appears in either result.

~~~sh
python -B round6/reduction/exact_bridge.py --alpha 1.5 --first 159.5 --nheight 48 --sub 2 --cells 128 --mesh 32
python -B round6/reduction/exact_bridge.py --alpha 1.5 --extra-base 30 --first 156.5 --nheight 24 --sub 1 --cells 32 --mesh 16 --param ".92,9.5,-3.5;1.1,8.75,-3.5"
~~~

The [verifier](exact_bridge.py) divides the compact physical interval into closed cells $a\le L\le b$. The lowest effective frequency is kept at its true value in the [polygonal envelope](../../round5/kernel/PROOF.md). Given the anchor $L_0$ and $d(L)=\log(1+4e^{-L/4})$, choose an integer $U_0\le36$ such that $d(L_0)e^{U_0}<.5$. All spectral envelopes under consideration equal 1 from $H$ through $e^{U_0}$. The upper cutoff is $u=\log t=50$, where $d(L_1)e^{50}>192$ and the envelope is exactly its certified inverse-square tail. Both inequalities are checked. Use log-height slabs of width $1/\mathrm{sub}$, divided into $\mathrm{nheight}$ cells each. At the first spectral decrement the cumulative zero sum includes the whole interval down to the verified height. No contribution from $H<\gamma<e^{U_0}$ is discarded.

In a slab $U\le\log t\le V$ and for a fixed triple $(\delta,W,\log h)$, apply the [finite-norm estimate](../../round5/kernel/FINITE_ANCHOR.md), using a short polynomial of length $2^{21}$ on closed cells of width at most $1/2$. The left norm takes the critical fourth-moment coefficient on the left endpoint rounded **down** to a multiple of $10^{-6}$. At $b=6$ the new coefficient is the [asymmetric sharp-cutoff estimate](../phase/PERIODIC_FOURTH.md) with $\alpha=3/2$. At $b=30$, the [partially folded modulus-30 mean](../folds/FOLD_MEAN.md) supplies a second complete left bound on the **same** function $f_{210}$, by factoring the Euler product as $\zeta E_b(E_{210/b}C_{210})$. Use the smaller valid left bound in each closed height cell. The right norm continues to use the modulus-210 function at the same $\delta,W,\log h$ and covers the full range $2\delta/V\le e\le2\delta/U$.

For each sampled cumulative upper ordinate $\log t=u$, each real node $s$, and each parameter triple use the exact pointwise exponents
$$
 \nu=\frac{2+4\delta/u}{2-s+3\delta/u},\qquad
 p=\frac{3(1-s+\delta/u)}{2-s+3\delta/u}.
$$
The detector bounds $\sum_{H<\gamma\le t}(\beta-s)_+$ by
$$
 \frac{c_\nu}{2\pi}\,\mathcal N^\nu (t u^2K_1)^p(uK_3)^{1-p}
        +E_{\mathrm{hor}}+E_{\mathrm{right}} .
$$
Here $c_\nu$ is the [degree-8 or triple-root degree-15 radial bound](../../round5/kernel/RADIAL.md). Both additional edges use the **same triple**, from the angular Jensen calculation in the [finite-grid proof](IRREGULAR.md). Taking the least upper bound over complete triples and chords over $s$ is valid. At the last node $s=7/8$ the true hinge equals zero. Below the first node .650 use the [explicit Riemann–von Mangoldt difference](../../round2/local/EXCEPTIONAL.md). The abscissa mesh in both displayed commands is .001.

The height sum, both signs of the ordinates, the verified initial zeros, the trivial zeros, and all prime powers are handled by the [finite-grid proof](IRREGULAR.md). Beyond $e^{50}$ the previous all-height detector gives the whole continuous tail, irrespective of the improved finite-interval coefficients. This proves the assertion on each full physical cell; the worst verified upper bound over the closed interval establishes the bridge. At $162.3$ the previous proof gives the remaining infinite half-line.

2026-11-20. Joint project attribution to Claude and Codex. Codex derived this compact-height transfer and its scalar verification.
