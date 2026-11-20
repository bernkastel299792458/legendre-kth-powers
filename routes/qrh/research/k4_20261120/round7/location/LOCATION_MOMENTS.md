# A sixth-moment obstruction for an empty fourth-power interval

Assume QRH(7/8), the published finite-height RH verification, and the analytic inputs of the [finite positive-part tables](../../round6/reduction/IRREGULAR.md). Write \(H_0=3\cdot10^{12}\), \(H=3000175332800\), and let \(L\) run over \(115,115.5,\ldots,148.5\). The established low and high endpoints imply that any unresolved empty gap lies inside at least one block \([L,L+1]\) in the logarithmic variable. Indeed its log length is at most \(4e^{-L/4}<1/2\) when its left endpoint belongs to \([L,L+1/2)\).

Set \(M=e^{(L+1)/4}, d=1/M, K(z)=(\sinh(dz/2)/(dz/2))^2\). The [tent explicit formula](../../round2/local/EXCEPTIONAL.md) shows that one empty interval gives a set of center locations of length at least \(2/M\). There the real sum of all zeros above \(H_0\), including conjugates, has absolute value at least \(D>0.99999\). This estimate includes the pole, trivial zeros, verified critical-line zeros and prime powers.

Truncate the positive ordinates at \(Y=e^{3L/8+15}\) and label zeros with multiplicity. Write
\[
a_\rho=e^{(\rho-1)L}K(\rho-1), \qquad
F(t)=\sum_{H_0<\gamma\le Y}a_\rho e^{(\beta-1)t+i\gamma t},\quad 0\le t\le1 .
\]
By \(N(u)\le u\log u\), partial integration, and \(|K|\le e^d(2M/\gamma)^2\), the discarded positive tail is bounded by \(B=2e^{d-L/8}(2M)^2(1+\log Y)/Y<0.000289244\). The absolute value of \(F\) on these locations is at least \(S=D/2-B>0.49971075\). For each integer \(k\ge1\) every failure forces
\[
\int_0^1 |F(t)|^{2k}\,dt\ \ge\ U_k,\qquad U_k=2 S^{2k}/M .
\]

## The coefficient square sum

Use the cumulative weight \(P(v)=\sum_{H<\gamma\le v}e^{2(\beta-1)L}\). Majorize the exponential by secant lines on the real-part grid and take the existing unconditional-in-the-rectangle-counts hinge bounds with their nonnegative slope jumps. This is the calculation in [the irregular-grid proof](../../round6/reduction/IRREGULAR.md) at exponent \(2L\), with an empty list of extra density hypotheses. Integrate \(P\) against \(-d\min(1,(2M/v)^4)\). On each finite log-height cell multiply the cumulative upper bound at its right endpoint by the full decrement on the cell. Above \(e^{55}\), \(P(v)\le e^{-L/4}v\log v\), giving at most \(4(2M)^4 e^{-165-L/4}(55/3+1/9)\). For \(H_0<\gamma\le H\) add \(H\log H\, e^{-L}\) by finite-height RH. Multiplication by \(e^{2d}\) bounds \(\sum |a_\rho|^2\) by \(V\). The eight-subdivision calculation gives \(V<0.000001172736\) on all 68 blocks. Each block retains its own \(V\) for the normalized comparisons below.

## Genuine off-diagonal terms

For ordered \(k\)-tuples of labeled zeros \(u,v\), let \(a_u=\prod_{\rho\in u}a_\rho\), \(\gamma_u=\sum_{\rho\in u}\gamma\), and \(r_u=\sum_{\rho\in u}(1-\beta)\). Write \(u\sim v\) for equal multisets of labels. The terms with \(u\sim v\) contribute at most \(k! V^k\). In the exact integral the remaining signed contribution is
\[
R_k=\Re\sum_{u\not\sim v}a_u\overline{a_v}
  \frac{\exp[-r_u-r_v+i(\gamma_u-\gamma_v)]-1}
       {-r_u-r_v+i(\gamma_u-\gamma_v)} .
\]
At \(k=3\), \(6V^3/U_3<0.001221\) on every block. An empty interval therefore forces \(R_3>0.998779 U_3\) on one of them. All these sums have finite, explicitly specified ranges.

A version using only positive weights can discard pairs with \(|\gamma_u-\gamma_v|\ge4\). Define
\[
E_k=\sum_{u,v}|a_ua_v|\,(1-|\gamma_u-\gamma_v|/4)_+ .
\]
On \([0,1]\) the function \(w(t)=\operatorname{sinc}^2(2(t-1/2))/\sin^2(1)\) majorizes 1, where \(\operatorname{sinc}(z)=\sin(z)/z\). The modulus of its angular-frequency Fourier transform is \(c_0(1-|\xi|/4)_+\), with \(c_0=\pi/(2\sin^2 1)\). By reflection and QRH every \(r_u\) is within \(r=3k/8\) of \(s=k/2\). Expand \(e^{-(r_u-s)t}\) in its power series in \(F(t)^k\). The triangle inequality in \(L^2[0,1]\), the bound on the Fourier transform of \(w\), and \(|r_u-s|\le r\) give
\[
\int_0^1 |F(t)|^{2k}\,dt\le C_k E_k,\qquad
C_k=c_0\left(\sum_{j\ge0}\frac{r^j}{j!}
                 \sup_{0\le t\le1} t^j e^{-st}\right)^2 .
\]
Indeed, for the \(j\)-th polynomial the whole-line integral against \(w\) bounds its squared norm by \(c_0 r^{2j}E_k\). For \(j\ge1\) evaluate the supremum at \(\min(1,j/s)\). After 32 terms the residual sum inside parentheses is at most \(4(3/4)^{33}\), using \(j!\ge(j/e)^j\). The diagonal of \(E_k\) is at most \(k!V^k\) again. This leaves only the contribution of **distinct multisets of ordinates with nearby sums** as an additional hypothesis. No estimate for that contribution is supplied by small diagonal size or by an assumption of independence.

The [verifier](location_moments.py) also implements a comparison using only the Chourasiya–Simonič density inequality for \(V\). At \(k=7\) its signed diagonal fraction is below .019440 and its positive weighted diagonal fraction is below .115327. In the stronger sixfold comparison just three positive ordinates occur on each side.

## An explicit alternative involving only sparse zeros

Use the [proved high endpoint \(147.2\)](../../round6/reduction/EXACT_BRIDGE.md) and take the 65 block starts \(115,115.5,\ldots,147\). In this variant all the correlations are confined to the same rectangle as the [million-zero necessary condition](../../round6/count/SINGLE_COUNT.md),
\[
\mathcal Z=\{\rho:\ .814<\beta\le 7/8,\quad H<\gamma\le H e^{37/4}\}.
\]
For \(j=1,2,3\), let \(B_j\) count ordered pairs of ordered \(j\)-tuples from \(\mathcal Z\), allowing repetitions within one tuple, with **no common zero label across the two tuples**, for which the two ordinate sums differ by less than 4 in absolute value. An empty fourth-power gap forces at least one of the following:

| Tuple length \(j\) | Necessary lower count in at least one row |
|---|---:|
| 1 | \(2\,655\,276\) |
| 2 | \(15\,968\,322\,816\,888\) |
| 3 | \(432\,136\,936\,418\,540\,421\,553\) |

Use tent width \(d=1.7/M\), leaving a center interval of length at least \(2(2-1.7)/M\). In the formula for \(D\), replace the width in all three errors by its new value. Put \(T_0=2/d\), \(Y=H e^{37/4}\). Remove \(\beta\le b=.814\) by majorizing their cumulative weight at each height both by \(e^{(b-1)L}N\) and by the exponential secant construction up to \(b\) extended linearly beyond \(b\). All its coefficients are nonnegative. Integrate the smaller bound against \(-d\min(1,(T_0/v)^2)\); its continuous integral above \(e^{55}\) contributes at most \(2T_0^2 e^{(b-1)L-55}(1+55)\) before the kernel factor \(e^d\). The verified zeros between \(H_0\) and \(H\) contribute at most \(e^d H\log H\,e^{-L/2}\). Independently, remove all ordinates greater than \(Y\) by the full cumulative-weight bound integrated against \(-d\min(1,(T_0/\max(v,Y))^2)\). Beyond \(e^{55}\) use the [infinite-height detector](../../round5/kernel/GRID_TARGET.md), whose tail kernel has precisely the same inverse-square form. Charging both discarded parts gives \(S>0.23026741\). Now \(U_3=2(2-1.7)S^6/M\) and \(C_3\) uses the actual range \(3/8\le r_u\le3(1-b)\). The positive diagonal \(C_3 6V^3\) is below \(0.111763\,U_3\) in every block.

Let \(P_j\) denote the contribution to \(E_j\) of pairs with no common label. Delete a maximal matching of common labels. The frequencies of matched terms cancel, the remaining pair has no common label, and there are at most \(\binom{3}{i}^2 i!\) ways to select and match \(i\) positions. Thus
\[
E_3\le P_3+9V P_2+18 V^2 P_1+6V^3,\qquad
P_j\le B_j\,e^{2j(d-L/8)} .
\]
Spend one third of \(U_3/C_3-6V^3\) on each of the three possible tuple lengths. The program computes all three resulting count thresholds separately on each block and rounds their minima down. Upper bounds for **all three** actual global counts strictly smaller than their tabulated values would exclude every counterexample. The disjunction alone asserts no further bound on the individual zero count.

~~~sh
python -B round7/location/location_moments.py
python -B round7/location/location_moments.py --slabs 8
python -B round7/location/location_moments.py --slabs 8 --through 294 --cut 814 --top-quarters 37 --width 1.7
~~~

The finite-height input is [Platt and Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765). The independent density input is [Chourasiya and Simonič v2, Corollary 1](https://arxiv.org/html/2507.15184v2#S1). All signed and absolute off-diagonal criteria here are open. The proofs of the location implications are analytic. Arb certifies the displayed scalar budgets.

Gafni and Tao use additive energy of zero ordinates to estimate the measure of exceptional short intervals. Their \(N^*(\sigma,T)\) counts near-equal sums of **two** ordinates on each side at tolerance 1 and their exponent bound is asymptotic in \(T\). The sixfold and finite-count criteria above have their own constants for the present heights. A separate [midpoint-phase criterion](ARITHMETIC_PHASE.md) keeps the phase of a specified candidate integer. [Gafni and Tao, §1.2](https://arxiv.org/html/2505.24017v1#S1.SS2)
