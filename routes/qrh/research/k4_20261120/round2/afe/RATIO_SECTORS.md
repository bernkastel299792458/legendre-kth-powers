# Three complete non-diagonal sectors in the common Gaussian window

Let \(\sigma=7/8,\ r=3/4,\ H=3\cdot10^{12},\ T\ge H,\ D=T/10\).
Use the sharp mollifier, \(I=\{|t|\ge H\}\), and the normalized Gaussian
\(W(t)=e^{-(t-2T)^2/D^2}/(\sqrt\pi D)\) of the
[common-window inequality](GAUSSIAN_WINDOW.md). Keep the two exact Gamma
weights of its square approximate functional equation (AFE).

For coprime positive \(a,b\), let \(\mathcal O_{a,b}\) consist of the terms
\(m=aj,\ n=bj\) for **all** \(j\ge1\), restricted to the true non-diagonal
condition \(da\ne eb\) on the mollifier indices \(d,e\le X\).
For \(\mathcal A=\{(1,1),(1,2),(2,1)\}\), the following bound holds:
\[
 X^r\sum_{(a,b)\in\mathcal A}
       \left|\int_I W(t)\mathcal O_{a,b}(t)\,dt\right|
 <\begin{cases}
     1.70\cdot10^{-9},&1\le X\le10^{10},\\
     1.71\cdot10^{-6},&1\le X\le\min(10^{14},T/300).
   \end{cases}                                                       \tag{1}
\]
In the first row \(X\le T/300\) follows from \(T\ge H\). To use the
whole common-window inequality, retain its additional condition \(X\le T^{7/8}\).
In particular, at its sample \(T=H,\ X=10^{10}\), the three sectors use
less than \(1.70\cdot10^{-9}\) of the dimensionless signed-integral
allowance of \(0.2100\). The other primitive ratios are still present.

## Summing the common factor with the actual weights

Write \(P=ab,\ U=|t|/(2\pi),\ q_t=h_t(1-\sigma)/h_t(\sigma)\), and
let \(V\) be the exact weight defined in the common-window note. The
arithmetic factor carrying the height frequencies is
\[
 B_{a,b}(t)=
 \sum_{\substack{d,e\le X\\ da\ne eb}}
 \frac{\mu(d)\mu(e)}{(de)^\sigma}e^{-it\log(da/(eb))}.
\]
The sector equals \(\Re B_{a,b}(t)\) times the real factor
\[
 A_P(t)=\sum_{j\ge1}\left[
  (Pj^2)^{-\sigma}V_{\sigma,t}(Pj^2)
  +q_t(Pj^2)^{\sigma-1}V_{1-\sigma,t}(Pj^2)\right].
\]
On the original Mellin lines \(\Re z=2\) this series is absolutely
convergent for every \(t\in I\). Summing \(j\) there gives respectively
\(\zeta(2\sigma+2z)\) and \(\zeta(2-2\sigma+2z)\). The direct and
reflected poles at \(z=\mp r/2\) cancel, because both carry \(P^{-1/2}\)
and the auxiliary function \(G_t\) is even. The residues at zero remain:
\[
 A_P(t)=P^{-\sigma}\zeta(2\sigma)+q_tP^{\sigma-1}\zeta(2-2\sigma)
                    +E_P(t),\qquad
 |E_P(t)|<802P^\sigma U^{-r-1}.                                     \tag{2}
\]
Here the stronger shift by 1 is possible because \(P\) is fixed. Shift
the direct line to \(-r-1\) and the reflected line to \(-1\). The only
crossed Gamma poles occur where \(G_t\) has a zero, as in the
[original diagonal proof](README.md). On putting \(v=-1+iu\), the common
integrand, with the differential \(dv/(2\pi i)\), is
\[
 P^{\sigma-1-v}\frac{h_t(1-\sigma+v)}{h_t(\sigma)}
 \zeta(1-r+2v)
 \left(\frac{G_t(v-r)}{v-r}+\frac{G_t(v)}v\right).
\]
In particular the first factor has modulus \(P^\sigma\).

Here are explicit bounds for (2). Put \(a_0=-7/8,\ w=-7/4+2iu\).
The Stirling bounds from §3 of the diagonal proof give, for \(|u|\le |t|/2\),
\[
 U^{r+1}\frac{|h_t(a_0+iu)|}{h_t(\sigma)}
 \le (1.001/.999)^2(3/4)^{-15/16}<2.
\]
The power of \(3/4\) comes from \(|t^2-u^2|\ge3t^2/4\). The same
proof gives \(|\log(q_t/U^{-r})|\le8/|t|\), by adding four errors
each at most \(2/|t|\). Thus \(|q_t/U^{-r}-1|\le9/H\).
[NIST DLMF, Stirling bounds](https://dlmf.nist.gov/5.11#ii).

For all \(u\) the sum of the absolute values of the two \(G_t(z)/z\)
is at most \(20e^{-.99u^2}\). Indeed the auxiliary polynomial costs
\(\exp(4((7/4)^2+u^2)/H^2)\), and the Gaussian and denominators
otherwise cost at most \([e^{(7/4)^2}/(7/4)+e]e^{-u^2}\).
Euler summation at 1 through the \(B_4\) correction yields
\[
 |\zeta(w)|\le |w-1|^{-1}+\tfrac12+|w|/12+
 |w(w+1)(w+2)|/720+
 |w(w+1)(w+2)(w+3)|/[720(3+\Re w)]
 \le5(1+|u|)^4.
\]
For the last inequality use \(|w+j|\le2(1+|u|)\) for \(0\le j\le3\).
[NIST DLMF, Euler–Maclaurin expansion](https://dlmf.nist.gov/25.2#iii).
Bounding \((1+|u|)^4\le8(1+u^4)\) and extending the central integral
over \(\mathbb R\) costs less than 801 in units of \(P^\sigma U^{-r-1}\).

On \(|u|\ge |t|/2\), Gamma recursion and the Euler integral give
\(|\Gamma((a_0+iy)/2)|\le2\Gamma(1+a_0/2)/|a_0|<100\).
The denominator's Stirling lower bound then gives
\(U^{r+1}|h_t(a_0+iu)|/h_t(\sigma)<10^5t^2e^{2|t|}\);
the power in \(|t|\) before rounding up is \(r+1+1-\sigma<2\).
After the other factors, the normalized integrand is bounded by
\(10^7t^2e^{2|t|}(1+|u|)^4e^{-.99u^2}<e^{-|u|}\).
This follows by taking logarithms and using \(2|u|\ge|t|\ge H\).
The two tails together cost less than 1. This proves (2).

## Gaussian frequency estimates

Set \(S=1+(X^{1-\sigma}-1)/(1-\sigma)\), an upper bound for
\(\sum_{d\le X}d^{-\sigma}\). For every retained pair
\[
 |\lambda|=|\log(da/(eb))|\ge 1/(\max(a,b)X),
 \qquad D|\lambda|\ge g=30/\max(a,b).
\]
This uses the unit gap between distinct positive integers, followed
by \(\log(k/j)\ge(k-j)/k\) for \(k>j\).
Each ordered-pair contribution to the constant term of (2), before its
arithmetic coefficient, has modulus bounded by
\[
 \left|\int_I W(t)e^{i\lambda t}\,dt\right|
 \le e^{-g^2/4}+20e^{-100}/\sqrt\pi .
\]
Indeed the full Fourier transform has modulus \(e^{-D^2\lambda^2/4}\)
and the omitted central band has length at most \(2T\) and Gaussian
height at most \(e^{-100}/(\sqrt\pi D)\).

For the varying power in (2) the corresponding bound is
\[
 \left|\int_I W(t)U^{-r}e^{i\lambda t}\,dt\right|
 \le (2\pi/H)^r
       \left[e^{25-5g}+5e^{-75}/\sqrt\pi+e^{-400}\right].           \tag{3}
\]
For \(t\ge H\), move the ray to \(t+5iD\,\mathrm{sgn}(\lambda)\).
Use the holomorphic power \((z/(2\pi))^{-r}\) in \(\Re z>0\).
On the translated ray the Gaussian gains \(e^{25}\), the frequency
loses \(e^{5D|\lambda|}\), and the power has modulus at most
\((2\pi/H)^r\). On the vertical joining segment, \((2T-H)/D\ge10\)
so the Gaussian costs at most \(e^{-75}/(\sqrt\pi D)\); the segment has
length \(5D\). The remote vertical side tends to zero by Gaussian decay.
The negative ray \(t\le-H\) has mass less than \(e^{-400}\) since its
distance to the center exceeds \(20D\). This proves (3).

For the error terms in (2) the mean absolute value of \(B_{a,b}\)
can be bounded without summing the absolute values of all its coefficients.
Before deleting \(da=eb\), the sum is
\(e^{-it\log(a/b)}|M_X(\sigma+it)|^2\).
The deleted coefficients have combined absolute value at most
\((ab)^{-\sigma}\sum_jj^{-2\sigma}\le\zeta(2\sigma)\), since
\((a,b)=1\). The full Gaussian mean of \(|M_X|^2\) is at most
\(\zeta(2\sigma)+S^2e^{-225}\) by the direct Gaussian transform
at its nonzero frequencies, using \(D/X\ge30\).
Thus \(\int_I W|B_{a,b}|\le J=2\zeta(2\sigma)+S^2e^{-225}\).

For each ordered sector the resulting upper bound consists of the
constant term \(X^r\zeta(2\sigma)P^{-\sigma}S^2(e^{-g^2/4}+20e^{-100}/\sqrt\pi)\)
and the following three terms, all multiplied by \((2\pi X/H)^r\):
\[
 |\zeta(1-r)|P^{\sigma-1}S^2(e^{25-5g}+5e^{-75}/\sqrt\pi+e^{-400}),
 \qquad |\zeta(1-r)|P^{\sigma-1}(9/H)J,\qquad
 802 P^\sigma(2\pi/H)J .
\]
The last two come from replacing \(q_t\) by \(U^{-r}\) and the
remainder \(E_P\), respectively. All these majorants increase with \(X\)
within either stated domain. The [Arb script](check_ratio_sectors.py)
returns total upper bounds below \(1.696134\cdot10^{-9}\) and
\(1.700615\cdot10^{-6}\) at the two endpoints. Reproduce with
\(\texttt{python -B check_ratio_sectors.py}\).

2026-11-20. Claude and Codex project attribution. Codex derived and
numerically checked the sector bounds on the QRH research route.
