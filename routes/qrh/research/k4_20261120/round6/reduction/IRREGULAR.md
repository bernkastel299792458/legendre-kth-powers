# Irregular finite zero-count conditions for the fourth-power gap

**Seven conditions suffice.** Assume QRH(7/8) and the verified analytic inputs below. At each of the seven pairs
$$
(k,1000s)=(5,854),(7,866),(9,835),(12,847),(14,825),(20,863),(33,853)
$$
suppose the true number of zeros with positive ordinate through $T_k=H\exp(k/4)$ and real part strictly greater than $s$ satisfies
$$
N_{>s}(T_k)\le 6\log(T_k)\,T_k^{3(1-s)/(3s-1)}.
$$
Then the entire interval $115.035950\le L\le150$ has normalized budget at most **.994630**. The largest cell bound starts at $116.160950$. This range overlaps the [proved high interval](../folds/MODULUS_2310.md) and meets the [proved low interval](../../round5/low/NARROW_COVER.md). In particular, a counterexample requires at least **390,987** nontrivial zeros with multiplicity in the open range
$$
.825<\beta\le7/8,\qquad H=3{,}000{,}175{,}332{,}800<\gamma<11{,}483{,}548{,}572{,}672{,}345 .
$$
The integer floors plus one of the seven respective right sides are $805225,390987,4947660,2421680,18554685,1244734,7746164$. The checker brackets all seven and the largest true tested ordinate at 200-bit precision.

In addition to the eight-condition analytic inputs, the [narrow-slab verifier](fine_intervals.py) uses complete detector bounds on $[j/2,(j+1)/2]$, $57\le j\le73$. Test $(\delta,W,\log h)$ equal to $(.92,9.5,-3.5)$, $(.80,8.5,-3)$, $(1.05,9,-3.5)$ and $(1.16,9,-3)$ with each of $Q=210,2310$. In each instance the cumulative bound includes the left, right and two edge terms for the same function $f_Q$ and the same triple. The short cores are $2^{21}$ and $2^{20}$ respectively. For $Q=2310$ use the [matched Euler factors](../folds/MODULUS_2310.md), folding base 210, depth 12, frequency cutoff $100T$ in the right variance, and include 11 in the angular Jensen product. The four-moment coefficient uses the [disjoint supports](../phase/SMOOTH_PHASE.md) of the two time windows, with $\alpha=1.25$, width .06 and harmonic prefix 384. Take the smallest complete upper bound at each effective height and abscissa, then the convex chords described below. At all other heights retain the eight-condition bounds. Both meshes are $1/32$.

~~~sh
python -B round6/reduction/irregular.py --seven
~~~

**Eight conditions suffice with the paired fourth moment.** The [rectangular verifier](irregular.py) covers the entire $115.035950\le L\le152$ interval with budget below **.987478** under the original $C=6$ assumptions at
$$
 (k,1000s)=(5,854),(7,835),(9,867),(10,815),(13,848),(17,830),(22,863),(36,854).
$$
At $L=152$ the [rectangle-free upper bridge](EXACT_BRIDGE.md) begins. For the eight-box calculation the normalized left coefficient in each height slab is tightened with both factorizations, $b=30$ and 210, short core $2^{21}$, folding depth 12 and the [disjoint-time fourth moment](../phase/SMOOTH_PHASE.md) at $\alpha=1.25$, width .06 and harmonic prefix 384. Each choice applies to the same unaltered interpolated function and right-side coefficient. Take the least complete left coefficient separately on each closed subinterval before taking the slab maximum. The original unfactored choice is also retained. The [coefficient checker](slabs.py) recomputes all fourteen sharper upper bounds for the slabs from 28.7 through 56 directly with Arb. Here both the physical mesh and log-height mesh have spacing $1/24$. Therefore any counterexample forces at least **419,084 positive-ordinate zeros** with $\beta>.815$ and $H<\gamma<24{,}310{,}672{,}519{,}119{,}809$. This follows by taking the smallest integer strictly above a right-hand side in the eight rectangles and the ceiling of their largest height. Both are checked at 200-bit precision. The count implication does not determine how many actual zeros are there.

~~~sh
python -B round6/reduction/irregular.py --eight
~~~


**Nine conditions suffice with the modulus-30 left mean.** Under the analytic inputs of the [periodic fourth moment](../phase/PERIODIC_FOURTH.md) and the [finite Gram estimate](../folds/FOLD_MEAN.md), use the same proof below with the additional complete left bound on every logarithmic slab. Use the same triples, right mean and edge costs as the eleven-condition variant, now permitting critical factorization with base 30, core length $2^{21}$ and folding depth 12. Inside each two-unit slab, split into cells of length at most $1/2$. The upper bound on the left is the largest of their certified split bounds. Each of the additional constants is recomputed from its source in nine-box mode. With physical and log-height spacing $1/48$, the total is at most **.991372** on $115.035950\le L\le155$. The rectangle pairs $(k,1000s)$ are $(5,866),(6,828),(7,849),(10,860),(11,814),(14,844),(20,833),(23,863),(37,854)$. The last true count is only at $H e^{37/4}$, after which only already proved bounds are used. Join the [modulus-30 rectangle-free upper coverage from $155$](../folds/BRIDGE.md). The older eleven-box variant reaches the earlier half-line directly without the periodic fourth-moment input.

~~~sh
python -B round6/reduction/irregular.py --nine
~~~

A counterexample therefore forces at least **339,119** true nontrivial zeros (positive ordinates, with multiplicity) in
$$
 .814<\beta\le7/8,\qquad
 3{,}000{,}175{,}332{,}800<\gamma<31{,}215{,}521{,}411{,}322{,}039 .
$$
Indeed some one of the nine inequalities must fail, and its rectangle is contained in this open-ended common height range and strict real-part strip. At 200-bit Arb precision the floors of the nine right-hand sides plus one, in the displayed order, are $339119,6660579,1375091,755166,36857291,3650124,15924519,1544814,9613571$. The first is their minimum. The highest true tested ordinate lies strictly between $31215521411322038$ and $31215521411322039$. The nine-box replay checks these integer inequalities separately.

Under QRH(7/8) and the analytic inputs of the [previous finite-box reduction](../../round5/kernel/GRID_TARGET.md), the middle interval $115.035950\le L=\log x\le162.3$ is covered if **11 outstanding count inequalities** hold. Write $H=3000175332800$, $T_k=H\exp(k/4)$, and count positive ordinates with multiplicities, including the top edge. At each selected pair require

$$
 N_{>s}(T_k)\le 6\log(T_k)\,T_k^{3(1-s)/(3s-1)} .
$$

The 11 pairs $(k,1000s)$ are $(5,867),(7,833),(7,852),(8,820),(10,862),(13,809),(13,846),(20,831),(23,864),(29,852),(46,856)$. The full 160-bit Arb bound is below **.995572**, with the worst physical cell starting at $127.754700$. The default calculation uses logarithmic height and physical spacing $1/32$ and the older residue-filtered fourth moment. The argument remains independent of the newer asymmetric fourth-moment calculation.

The following alternate 13 pairs give a larger margin:

| $k$ | $1000s$ |
|---:|:---|
| 5 | 854 |
| 6 | 867 |
| 7 | 800 |
| 8 | 836 |
| 9 | 824, 847 |
| 12 | 864 |
| 14 | 816 |
| 16 | 849 |
| 21 | 833 |
| 25 | 863 |
| 30 | 847 |
| 47 | 857 |

Its full budget is less than **.942336**. All conditions in the two lists belong to the [original 4,950](../../round5/spectrum/DENSITY_TARGET.md). There is also a direct reduction of the [former 30](../../round5/kernel/GRID_TARGET.md) to a strict subset of **17**. Retain $837,852,865$ at $k=4$; all five at $k=9$; $820,837,852,865$ at $k=17$; $837,852,865$ at $k=30$; and $852,865$ at $k=51$. Its cost is less than **.982830**. The endpoint results used for completion reach [115.035950](../../round5/low/NARROW_COVER.md) and [162.3](../../round5/kernel/FINITE_ANCHOR.md), both inclusively. The finite lists themselves remain outstanding.

~~~sh
python -B round6/reduction/irregular.py
python -B round6/reduction/irregular.py --nheight 16 --cell 1/8 --grid 5:854,6:867,7:800,8:836,9:824,9:847,12:864,14:816,16:849,21:833,25:863,30:847,47:857
python -B round6/reduction/irregular.py --nheight 16 --cell 1/8 --grid 4:837,4:852,4:865,9:800,9:820,9:837,9:852,9:865,17:820,17:837,17:852,17:865,30:837,30:852,30:865,51:852,51:865
~~~

## Combining bounds on a cumulative count and on its integrals

Set $A_s(t)=\sum_{H<\gamma\le t}(\beta-s)_+$. At a true evaluation point $t$, a tested rectangle at $(s',T)$ supplies the same upper bound $C$ for the number with $\beta>v$ whenever $t\le T,\ v\ge s'$. Take the least applicable bound across **all later heights and weaker real abscissae**. At $t=H+32$ the [verified zero-free rectangle](../../round5/low/ZERO_FREE_PATCH.md) supplies zero for $s\ge.800$. Through $H+5000000$ use the coefficient-7 bounds on all 75 nodes, and through $H+6500000$ the applicable coefficient-6 bounds on six nodes from the [short-window certificate](../../round5/low/FINITE_POINTS.md). Each of those short-window bounds uses the corresponding target value at $H$, as established in that proof.

Start with the known analytic upper bounds $B_j(t)$ on $A_{s_j}(t)$, for $s_j=.650+.001j$. QRH gives $A_{.875}(t)=0$. Descending in $j$, if the applicable count limit is $C_j$, replace the current upper bound at $s_j$ by

$$
 \min\{B_j(t),\ B_{j+1}(t)+(s_{j+1}-s_j)C_j\}.
$$

Indeed $A_{s_j}(t)-A_{s_{j+1}}(t)$ integrates the actual strict real-part count from $s_j$ through $s_{j+1}$. Afterwards take chords between the resulting bounds, since the true function is convex. This construction uses the analytic positive-part moments through $7/8$, including those above individual tested abscissae.

## Analytic inputs and normalized sum

For $u=\log t$ through 55 split the range into the slabs $[28.7,30],[30,32],\dots,[54,56]$. The [slab calculation](slabs.py) uses $\delta=.92,W=9.5,\log h=-3.5,Q=210$, short core $2^{15}$ and 16 Mellin cells, with the [filtered fourth moment](../../round5/left/UNIT_DIAGONAL.md) and the [local height norm](../../round5/kernel/FINITE_ANCHOR.md). At each evaluation $u$ take the actual exponents

$$
 \nu=(2+4\delta/u)/(2-s+3\delta/u),\qquad
 p=3(1-s+\delta/u)/(2-s+3\delta/u).
$$

The interpolated side is at most $c_\nu \mathcal N^\nu(tu^2K_1)^p(uK_3)^{1-p}/(2\pi)$ with the [certified radial detector](../../round5/kernel/RADIAL.md). Lower frequencies use finite-height RH with both signs included. The base count above $H$ uses $F(t)-F(H)+.15\log(tH)+6$, $F(t)=t(\log(t/(2\pi))-1)/(2\pi)$, from the [explicit total-count estimate](../../round2/local/EXCEPTIONAL.md).

The old complete edge bound is always available. The new option takes the [angular Jensen formula](../../round5/low/NARROW_COVER.md) for both horizontal edges of the rectangle with its taper built at $t$. On a slab $U\le\log t\le V$ use $Y\ge e^{U+\log h},\ X\le e^{V+\log h+W}$ and an integer $\lceil e^V+6\rceil\le e^V+7$ for the Euler-summation estimate. On the right the bound is $4(U+\log h+2)^2e^{-U-2\log h}/\pi$, since its expression as a function of $u$ decreases. For the horizontal edges take circle radius 1.86, 96 upper semicircle cells and 48 steps in the angular denominator, evaluated at $d=1.35\ge2-s$. The radial polynomials obey $\deg P/m\le8$, where $m$ is their guaranteed multiplicity, and $|P(w)|\le(1+|w|)^{\deg P}$. Their real part at the center exceeds $1/2$ by $(1+a_2)^{15}<3/2$, $a_2=2(\log Y+2)/Y$. This charges both edges of each same detector including the multiplicity normalization.

For $L\in[a,b]$, freeze the positive exponential in the zero real parts at $a$ and the scale $d=\log(1+4e^{-b/4})$ at $b$. A step of the [polygonal spectral majorant](../../round5/kernel/PROOF.md) between adjacent heights uses the cumulative bound at the later height, including that upper ordinate. Insert the three short-height endpoints before the ordinary logarithmic grid. The abscissa mesh is .001. The 13- and 17-box replays use logarithmic height spacing $1/16$ and physical spacing $1/8$. From $u=55$ onwards use the integrated analytic tail from the [former grid proof](../../round5/kernel/GRID_TARGET.md), without a conditional count. The verified zeros, trivial zeros and prime powers have the same charges as in that proof. The [interval-arithmetic verification](irregular.py) covers the entire closed interval. Its conclusion $x<p<x+4x^{3/4}$ gives the required strict inequalities for $x=n^4$.

2026-11-20. Joint project attribution to Claude and Codex. Codex derived this finite reduction and its scalar checks.
