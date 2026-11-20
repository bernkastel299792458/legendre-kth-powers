# A common window for the sharp-mollifier estimates

Put \(H=3\cdot10^{12},\ 7/10\le\sigma\le7/8,\ r=2\sigma-1,\ T\ge H\),
\(1\le X\le\min(T^{7/8},10^{14})\). Use the sharp coefficients
\(\mu(d)\mathbf1_{d\le X}\). Choose the probability density
\[
 W_T(t)=\frac1{\sqrt\pi D}\exp(-(t-2T)^2/D^2),\qquad D=T/10.
\]
Thus \(T\) is a scale; the center is \(2T\). Write \(I=\{|t|\ge H\}\),
\(Q_X=R_1-1=\sum_{n>X,\ n\ge2}|\sum_{d\mid n,\,d\le X}\mu(d)|^2/n^{2\sigma}\).
In the sharp square AFE let \(\mathcal O_X(t)\) be the sum of the two
non-diagonal parts, retaining both signs and the exact Gamma weights
from the [diagonal lemma](README.md). In particular
\(|\zeta M_X|^2=1+Q_X+R_2(t)+\mathcal E(t)+\mathcal O_X(t)\) on \(I\).
Reflection about \(t=0\) gives the lemma at negative heights as all
the mollifier coefficients are real and the AFE is conjugation symmetric.

For any desired dimensionless variance budget \(B=B(\sigma,T,X)\), a
**sufficient remaining signed inequality** is
\[
 \boxed{\quad
 X^r\left[Q_X+\int_I W_T(t)\big(\mathcal O_X(t)+R_2(t)\big)\,dt\right]
       \le B-\epsilon_\sigma,\qquad
 \epsilon_\sigma=\begin{cases}
 .078545,&.85\le\sigma\le7/8,\\
 .263337,&.70\le\sigma<.85 .
 \end{cases}\quad}                                                    \tag{1}
\]
If (1) holds, the proved conclusion is
\(\int_{\mathbb R}W_T(t)|\zeta M_X-1|^2(\sigma+it)\,dt\le BX^{-r}\).
The implication is proved here; (1) remains a target. The complete
reflected residue \(R_2\le0\) can also be dropped for a stronger sufficient
condition. The positive tail \(Q_X\) must be retained or upper bounded.
The fifth-power Theorem A uses exactly \(\kappa_1=rX^rQ_X\), so its
grid entries contribute \(\kappa_1/r\) when their hypotheses and numerical
certificate apply. For example the existing H3-free sharp table at
\(\sigma=7/8,\ X=10^{10}\) reports \(\kappa_1<.533564\). Taking that
arithmetic input, \(B=1\) would leave more than \(0.2100\) for the scaled
signed integral in (1). This numerical example specifies a target; it
does not assert that \(B=1\) holds or would suffice for every detector.
The underlying fifth-power table was not recomputed here.

At that same sample the actual primitive AFE ratios \(m/n=1,2,1/2\),
including all common multiples and deleting the true diagonal, have
combined scaled cost below \(1.70\cdot10^{-9}\). The other ratios and
the complete signed reflected residue still enter (1).
[Three-sector estimate](RATIO_SECTORS.md)

Explicitly put
\[
 V_{a,t}(n)=\frac1{2\pi i}\int_{(2)}
   \frac{h_t(a+z)}{h_t(a)}G_t(z)n^{-z}\frac{dz}{z},
 \qquad q_t=\frac{h_t(1-\sigma)}{h_t(\sigma)} .
 \]
Then \(\mathcal O_X(t)\) is the real sum over \(d,e\le X,\ m,n\ge1,\ dm\ne en\)
with summand
\[
 \frac{\mu(d)\mu(e)}{(de)^\sigma}
 \cos\!\left(t\log\frac{dm}{en}\right)
 \left[
 (mn)^{-\sigma} V_{\sigma,t}(mn)
   +q_t(mn)^{\sigma-1}V_{1-\sigma,t}(mn)
 \right].
\]
The real part follows by exchanging \((d,m)\) and \((e,n)\); the reflected
sum is indexed after interchanging its two zeta summation variables.
For every fixed \(t\in I\) both sums converge absolutely on the indicated
initial Mellin line. The integrated quantity is defined by taking the
complete sum first as above. A later proof which interchanges the height
integral with the summations must justify that interchange.

## Proved costs in the implication

Expand \(|\zeta M_X-1|^2=|\zeta M_X|^2-1-2\Re(\zeta M_X-1)\).
On \(I\) the integral of \(Q_X\) is at most \(Q_X\). The complete
first-moment cost on the entire axis is bounded by \(1.81\cdot10^{-8}X^{-r}\)
by the [first-moment lemma](FIRST_MOMENT.md).

For \(|t|\ge T\), after multiplying by \(X^r\) the pointwise diagonal
error is bounded by \(c(2\pi X/T)^r\le c(2\pi H^{-1/8})^r\), where
\(c=.531\) throughout the strip and \(c=.268\) on the upper substrip.
The base is less than 1. The worst exponents are respectively \(r=.4\)
and \(r=.7\), giving upper bounds \(0.2633362\) and \(0.0785440\).
The Gaussian mass of \([-T,T]\) is at most
\(20e^{-100}/\sqrt{\pi}\). On \(H\le |t|<T\), use
\(c(2\pi X/H)^r\le .531(2\pi\,10^{14}/H)^{3/4}\), which costs less
than \(2\cdot10^{-41}\) after integration.

It remains to pay for \(|t|<H\), since the pointwise diagonal result was
proved only for \(|t|\ge H\). Euler summation at \(N=H\), including its
pole and fractional-part remainder, gives
\[
 |\zeta(\sigma+it)|
 \le 1+8H^{.3}+8H^{.3}+\frac{H+1}{.7H}H^{.3}
 \le 19H^{.3}.
\]
Here \(|\sigma+it-1|\ge1/8\); the modulus of the remainder is bounded by
\(|\sigma+it|H^{-\sigma}/\sigma\). Also \(|M_X|\le1+8X^{.3}\le9X^{.3}\).
The upper contribution to \(X^r\int_{|t|<H}W_T(|\zeta M_X|^2-1)\)
therefore costs at most
\[
 \frac{20e^{-100}}{\sqrt{\pi}}19^2\,9^2 H^{.6}(10^{14})^{1.35}
 < 3.0\cdot10^{-12}.
\]
Adding these pieces proves the implication, including the full low band.
The [Arb script](check_first_moment.py) checks the rounded constants.

The same Gaussian would control the uniform mean on \([1.9T,2.1T]\) at
cost \(\exp(1)\sqrt\pi/2\), since its normalized density is at least
\(e^{-1}/(\sqrt\pi D)\) there. The detector requires explicit control
over its entire height range. This local comparison starts at \(1.9H\);
the contribution below that altitude and the sum of several windows
need their own bounds. A Gaussian centered at zero gives no exponentially
small mass for \(|t|<H\) when its width is comparable to \(H\).

## Independent check of the flat/fine BV transfer

This transfer uses the BV taper with \(Y=hT,\ X=e^WY\). At its right
abscissa the proved cumulative bound is
\[
 \int_0^Z |f(1+\delta/U+it)|^2\,dt\le
 \pi m_0 S(1+e)+(Z+\pi m_0/2)S(2+e),\quad
 U=\log T,\ e=2\delta/U.
\]
Freeze \(T\) in the coefficients. The [flat window](../spectrum/PROOF.md)
has \(G(t)=\min(1,(vT/t)^m)\) on the positive axis, and \(-dG\) is a
probability measure of mean \(\bar yT\), \(\bar y=vm/(m-1)\).
Integration of this affine majorant replaces \(Z\) with \(\bar y T\).
In a [fine right-endpoint cell](../right/fine/PROOF.md) let
\(l\le e\le u,\ S(1+e)/U\le A,\ TS(2+e)\le B'\).
The resulting right moment divided by \(U\) is at most
\[
 \pi m_0 A+
  (\bar y+\pi m_0/(2e^{U_0})) B'\,u/(2\delta).
\]
The implementation computes its maximum over the cells with
\(\kappa=\pi/(8\bar y^2)\), since
\(\sqrt\pi/(2\sqrt{2\kappa})=\bar y\). Only the constant returned by
the arithmetic function \(\mathtt{right\_endpoint}\) is needed here.
The left \(4/3\)-moment and the comparison factor for Gabriel interpolation
are supplied by the flat window. The same calculation works for either
of the fine proof's two estimates for \(TS(2+e)\), provided the chosen
version is passed to the endpoint routine.

The sharp AFE and the BV interpolation are two different mollifier choices.
Combining bounds on their respective zero counts requires a pointwise
minimum or a new detector argument. Their moment terms cannot be added
as if they bounded different parts of the variance for a single mollifier.

2026-11-20. Claude and Codex project attribution. Codex derived the common
sharp window and reviewed the separate BV transfer.
