# Testing whether the other finite inequalities force an individual count

**New direct upper counts on the actual six boxes.** With the same QRH and analytic inputs, the integer bounds are \(17\,144\,450;\ 6\,633\,773;\ 147\,037\,821;\ 62\,654\,574;\ 23\,993\,118;\ 149\,798\,707\) in increasing order of the six heights. These are the floors of actual interval upper endpoints, using the moving-endpoint critical fourth moment, the auxiliary short core, and the right-boundary arithmetic variance. The previous rational-fourth version gave \(17\,410\,733;\ 6\,725\,155;\ 149\,527\,288;\ 64\,371\,222;\ 25\,374\,973;\ 157\,521\,985\). The gap parameters \(4000(s-v)\) in the latest scan are \(54,54,57,52,50,46\). In particular the two-million-scale and larger bounds still do not prove the six input inequalities.

~~~powershell
python -B round6/reduction/actual_boxes.py --rational --scan
python -B round6/reduction/actual_boxes.py --sweep --scan
~~~

**Direct upper bounds at the six true heights.** In the order of the table below, the numbers of positive-ordinate zeros with $\gamma\le T_k$ and $\beta>s$ are respectively bounded by
$$
17{,}499{,}504,\quad6{,}768{,}868,\quad150{,}226{,}960,\quad
65{,}144{,}864,\quad25{,}741{,}660,\quad160{,}413{,}149.
$$
These bounds use QRH(7/8) and the analytic estimates, with no unproved finite count input. At $u=\log T_k$ take $U=V=u$ in the [matched modulus-2310 detector](EXACT_BRIDGE.md). Use critical factor $\zeta E_{210}$, core $2^{20}$, depth 12 and the [centered fourth moment](../phase/CENTERED_PHASE.md). Compute the right side by the [real-variable Mellin estimate](../../round7/taper/mellin_bridge.py) at the single true exponent, with 128 right cells. At $v=s-j/4000$ use $N_{>s}(T_k)\le A_v(T_k)/(s-v)$, because every counted zero contributes at least $s-v$ to the hinge. The direct integer upper bounds also hold when the real edge $\beta=s$ is included. The left, right, radial, angular and vertical edge terms all use the same detector triple. Select $(j,\delta,W,\log h)$ as follows in increasing $k$:
$$
(54,1.1,8.5,-2.25),\ (54,1.1,8.5,-2.25),\ (57,1.22,8.5,-2.5),\
(52,1.1,8.5,-2.25),\ (49,1.16,9,-2.5),\ (46,1.16,9,-2.5).
$$
The [pointwise count verifier](actual_boxes.py) checks that each real-valued upper bound is strictly below the displayed integer plus one. The following independent population test uses the previous finite slab rows; its last column refers to those slab bounds.

For scale, write the ratio of each new real upper bound to its required count limit as $T_k^{d_k}$. The six finite-height values of $d_k$ round to $.09183,.09120,.08590,.09100,.09263,.09469$. This comparison records the size of the remaining numerical gaps at their individual heights.

~~~sh
python -B round6/reduction/actual_boxes.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived the finite count comparisons and test populations.

The six candidate rectangles have $(k,1000s)=(6,851),(7,865),(9,826),(12,842),(19,863),(31,856)$ and $T_k=H e^{k/4}$. Take all upper bounds on the real-part hinges and total counts in the finite $1/16$ log-height mesh through $\log t=55$ of the [coupled reduction](COUPLED.md), including its stronger half-unit rows, translated initial windows and [sharper modulus-2310 right mean](../../round7/taper/mellin_bridge.py). These finite scalar bounds and the other five count conditions do not imply the individual omitted condition, even if the test populations satisfy reflection and conjugation symmetry.

Write $r_i$ for the smallest integer strictly greater than the right side of the omitted count. Put $\beta_*=s+10^{-6}<7/8$. Take $m_i r_i$ distinct positive ordinates in $[T_k-10^9,T_k]$, each carrying a zero at each of $\beta_*$ and $1-\beta_*$. Reflect to the negative ordinates. The whole interval is contained strictly after the preceding height node; this is checked for each $k$. Before that node the population is empty. At each subsequent height the total positive count is $2m_i r_i$, and the contribution to the proved hinge at any node $v\ge.650$ is exactly $m_i r_i(\beta_*-v)_+$. For any other selected count rectangle active at $T_k$ and containing $\beta_*$, compare the mass directly to its true right side. The [160-bit verifier](box_obstruction.py) checks all these inequalities.

| $k$ | $s$ | $r_i$ | Factor $m_i$ preserving the five other counts | Analytic hinge/total allowance divided by $r_i$, rounded down | Direct rigorous upper bound for the true count at $T_k$ |
|---:|---:|---:|---:|---:|---:|
| 6 | .851 | 1,089,900 | 3 | 16.94 | 18,473,370 |
| 7 | .865 | 420,071 | 2 | 16.96 | 7,196,025 |
| 9 | .826 | 10,495,930 | 15 | 15.03 | 157,825,660 |
| 12 | .842 | 3,630,069 | 18 | 18.43 | 66,932,550 |
| 19 | .863 | 1,158,145 | 4 | 22.78 | 26,385,740 |
| 31 | .856 | 5,070,970 | 32 | 32.18 | 163,220,660 |

The allowance column takes the minimum of $D(t)/2$ and all $A_v(t)/(\beta_*-v)$ at every later finite node, omitting $v\ge\beta_*$. The direct upper count instead uses the terminal $D(T_k)$ and $A_v(T_k)/(s-v)$ for $v<s$. Its entries are rounded upwards. The constructed measures certify non-implication for the specified finite inequalities. They are not proposed zeta zero sets, and they impose no obstruction on additional analytic estimates.

The six can also fail **simultaneously by a factor larger than three** within these analytic constraints. Superpose three copies of each $r_i$ reflected population, disregarding the five conditional count limits when forming this single joint example. For each analytic row, the ratio to its allowable upper bound is at most
$$
3(1/16.94+1/16.96+1/15.03+1/18.43+1/22.78+1/32.18)
<.941282 .
$$
Each omitted population already vanishes before its own height cell, so this same bound covers the early nodes as well. At the $i$-th tested rectangle the sum contains at least $3r_i$ positive zeros with real part strictly greater than its threshold. The short proved count windows ending close to $H$ remain empty for this test population.

The same simultaneous witness satisfies all twenty-one [translated increment windows](LOCAL_CALLS.md), of log widths $1/16,2/16,4/16$ after $H$ and after each of the six count heights. Only $(T_6,T_7]$ contains any of these populations. It contains the second population, whose real-part hinge uses less than **.175149** of every one of the $226$ verified local upper bounds in the $.001$ abscissa mesh, including the optional short-core improvement. All other local upper bounds see zero. This further test concerns the simultaneous witness with multiplicity $3r_i$.

That witness also uses less than **.306** of each of the six additional exact-height hinges supplying the sharper integers at the top of the page. The pointwise count verifier recomputes this ratio at each of its six specified $(T_k,v)$ pairs.

~~~sh
python -B round6/reduction/box_obstruction.py
~~~
