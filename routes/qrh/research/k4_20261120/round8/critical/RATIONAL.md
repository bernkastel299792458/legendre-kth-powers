# Rational frequencies of the genuine AFE interference

For \(Q=210,\alpha=1,w=.04,Z=384\), the [verifier](rational_fourth.py) bounds the complete normalized fourth moment on each closed half-line:

| \(U\) | Centered phase bound | After removing the short product | After also projecting onto rational frequencies |
|---:|---:|---:|---:|
|35|.001260749|.001207338|.001178156|
|37|.001106399|.001056038|.001027044|
|40|.000954756|.000907721|.000879727|

All columns use the same \(\zeta E_{210}\). The final column tests all reduced \(1\le s<r\le512\) with \((rs,Q)=1\) and keeps a nonnegative coefficient only when its signed estimate saves enough. It uses the [short-product bound](INTERFERENCE.md) from \(U+1\) onward.

## A single rational saddle

Use the notation \(W,V,S,X,Y\) of [the short-product estimate](INTERFERENCE.md). Fix one paired cutoff, write \(\lambda=X/Y\), and let \(R=r/s>1,\ \omega=\log R\). We estimate \(E[V\cos(\omega t)]\). On the extended natural support \(n\le X(t), j\le Y(t)\), one orientation \(W e^{i\omega t}\) has increasing phase derivative at least \(\omega\). Extending both orientations below the AFE start costs at most \(2t_0 L_f(t_0)L_d(t_0)/T\). The elementary coefficient-sum bounds \(L_f,L_d\) include the dual \(Q^{-1/2}\).

For \(W e^{-i\omega t}\) each pair has stationary time \(a=2\pi Rnj/Q\). Apart from the factor \(e^{-i\pi/4}\), its phase is \(t\log(t/a)-t\). The natural lower endpoint is \(l=(2\pi/Q)\max(n^2/\lambda,\lambda j^2)\). With \(C=QT/(2\pi R)\), the saddle belongs to the active interval precisely when
\[
 |\log(n/(\lambda j))|\le\omega,\qquad nj\le C .
\]
Its principal integral is \(\sqrt{2\pi a}\,e^{-ia}\) with the AFE factor included. For the arithmetic sum use the half-open lower \(j\)-endpoint; any change at equality is covered in the boundary estimates below.

Here are explicit estimates for this replacement. If both \(|\log(l/a)|,|\log(T/a)|\) exceed \(0<\epsilon<.1\), then its absolute integral error is at most \(4000+8/\epsilon\). When the saddle is outside the interval, the monotone first derivative alone gives \(2/\epsilon\). For an interior saddle, first evaluate the reference segment \(a/2\le t\le3a/2\). With \(x=t/a\), set
\[
 v=\operatorname{sgn}(x-1)\sqrt{2(x\log x-x+1)}
  =(x-1)h(x),\quad
 h^2=2\int_0^1\frac{1-z}{1+z(x-1)}\,dz,\quad
 g=\int_0^1\frac{dz}{1+z(x-1)} .
\]
Then \(A(v)=dx/dv=h/g,\ A(0)=1\). On \(1/2\le x\le3/2\), each of \(g,h^2\) lies in \([2/3,2]\), with first and second absolute derivatives bounded by 4 and 16. Hence \(|h'|<3, |h''|<20,\ |A|<3,\ |A_x|<18,\ |A_{xx}|<300\), by differentiation of the quotient. In the \(v\) variable this gives \(|A'|\le54,\ |A''|\le3672\). Write \(A(v)=1+vB(v)\). Divided differences give \(|B|\le54,\ |B'|\le1836\). Integration by parts of \(a\int vB(v)e^{iav^2/2}dv\) costs at most \(108+1836\sqrt2\). The two tails completing the constant-amplitude Fresnel integral each cost at most \(2/|v_{\rm end}|<5\), since \(|v_{\rm end}|\ge\sqrt{2/3}/2\). The resulting full Fresnel integral, after \(a e^{-ia-i\pi/4}\), is the stated principal value. Changing either endpoint to its actual one costs at most \(2/\min(\epsilon,\log(3/2))\) by monotone differentiation. This proves the claimed error. The Gaussian integral with positive damping and passage to zero damping supplies the Fresnel value. [Fresnel integrals](https://dlmf.nist.gov/7.2#iii)

For arbitrary endpoints the integral minus the principal term, whether included or omitted, is at most \(9\sqrt a+9\). Split at \(|\log(t/a)|=\min(1,\sqrt{2/a})\). For \(a\ge2\), the central length and two first-derivative estimates cost at most \(2\sqrt{2a}\sinh(1)+2\sqrt{2a}<6.2\sqrt a\); the principal term costs another \(\sqrt{2\pi a}\). For \(a<2\) the central length and tails cost at most \(2a\sinh(1)+4<9\).

Thus the ordinary error for both orientations is bounded by
\[
 (2/\omega+4000+8/\epsilon)L_f(T)L_d(T)/T ,
\]
and in the union of the lower and upper boundary strips one adds \(9\sqrt a\) times the coefficient modulus. The constant \(9\) in that estimate is already covered by the ordinary error. The verifier fixes \(\epsilon=e^{-U/4}\) on a slab.

## Counting the boundary contributions

Write \(\rho=\varphi(Q)/Q,\ \mu=Q^{-1}\sum_{j\bmod Q}|c_Q(j)|\). Let \(D_f,D_d\) be the interval discrepancies of the units and of the unscaled absolute Ramanujan sequence. The weight \(\sqrt a\,|c_Q(j)|/\sqrt{Qnj}\) equals \(\sqrt{2\pi R}\,|c_Q(j)|/Q\) for every pair. In the lower-boundary strips write \(b=R\) or \(1/R\). For each \(j\), the \(n\)-interval has length \(2\lambda j b\sinh\epsilon\), and \(j\le Y_b=Y(T)\min(1,e^\epsilon/b)\). Its weighted count is bounded by
\[
 2\rho b\sinh\epsilon\,\lambda(\mu Y_b^2/2+D_dY_b)
     +D_f(\mu Y_b+D_d).
\]
The first-moment bound follows by integrating the interval counts on \([x,Y_b]\). Use the exact identity \(\lambda Y(T)^2=QT/(2\pi)\) in the quadratic term before bounding the cutoff parameter. For the upper-boundary strip \(C e^{-\epsilon}\le nj\le C e^\epsilon\), the corresponding count is at most
\[
 2\rho C\sinh\epsilon\,\{\mu(1+\log Y(T))+D_d\}
             +D_f(\mu Y(T)+D_d)
\]
by the harmonic upper bound for the absolute dual coefficients. Multiply the three counts by \(9\sqrt{2\pi R}/(QT)\). Interval discrepancies cover endpoints by continuity in their geometric lengths.

## The arithmetic principal term

The principal contribution is \(2\pi\sqrt R/(QT)\) times the signed sum of
\[
 \mathbf1_{(n,Q)=1}\, c_Q(j)e^{-2\pi i r n j/(Qs)}
\]
in the saddle domain. At fixed unit \(n\), the complex \(j\)-sequence has period \(Qs\). Its mean equals \(1\) if \(s\mid n\), and zero otherwise: expand \(c_Q(j)=\sum_{(h,Q)=1}e^{2\pi ihj/Q}\), then use that \((r,s)=1\) and both \(r,s\) are units modulo \(Q\). For an arbitrary half-open interval of length \(L(n)\), the error after its complete periods has absolute value at most \(Qs(\mu+1)\). The actual length as a function of real \(n>0\) is
\[
 L(n)=\left[\min(Rn/\lambda,C/n)-n/(\lambda R)\right]_+ .
\]
It is unimodal, supported on \(n\le X(T)\), with maximum at most \(Y(T)\). Its integral equals \(C\log R\), either directly or by the variables \(nj,\log(n/(\lambda j))\) with Jacobian \(1/2\). Applying interval discrepancy by layer-cake to the surviving \(s\)-multiples yields the upper bound
\[
 \frac{\rho\log R}{\sqrt{rs}}
 + \frac{2\pi\sqrt R}{QT}
   [D_fY(T)+(\rho X(T)+D_f)Qs(\mu+1)] .
\]
Together with the error bounds this gives \(h_{r,s}\ge E[V\cos(\omega t)]\) in [the stationary verifier](stationary.py). Uniformity on \(U\le\log T\le U+b\) uses the largest possible \(\log Y(T)\) in the leading upper-boundary term. All the other time-dependent errors decrease after division by \(T\).

## Rational component of the squared amplitudes

For either sharp polynomial, equal frequencies against \(e^{-i\omega t}\) have indices \(sk,rk\). Their coefficient is positive with raw weight equal to the square of the original sequence at \(k\): for units \(r,s\), \(c_Q(rk)c_Q(sk)=c_Q(k)^2\). Their moving cutoff is \(Y_{\rm branch}(t)/r\). Take the usual [periodic harmonic lower mean](../../round6/phase/CENTERED_PHASE.md) at the smallest allowed endpoint length divided by \(r\) and divide by \(\sqrt{rs}\). Off the exact diagonal, with the numerical limits of the two sequences denoted by \(X',Y'\), one has the following upper bound before multiplying by the squared coefficient maximum:
\[
 \frac2T\sum_{\substack{n\le X',m\le Y'\\rn\ne sm}}
 \frac1{\sqrt{nm}\,|\log(rn/(sm))|}
 \ \le\
 \frac{4\sqrt{rs}\,X'[1+(1+\log Y')/s]+8\sqrt{X'Y'}}T .
\]
Indeed \(1/(\sqrt{ij}|\log(i/j)|)\le1/|i-j|+1/\sqrt{ij}\). For fixed \(n\), the nonzero distances \(|rn-sm|\), counted on each side, have a first term at least one and subsequent spacing \(s\). Each pair has just one time interval and hence an oscillatory integral bounded by \(2/|\log(rn/(sm))|\). This proves a lower bound for \(E[S\cos(\omega t)]\) for the same sharp polynomial.

## Joint projection on the finite set of frequencies

Set \(P(t)=\sum p_{r,s}\cos(t\log(r/s))\) with nonnegative coefficients. Let \(l_{r,s}\) denote the proved lower bound on \(E[S\cos(\omega t)]\) minus \(m/(T\omega)\), giving \(E[(S-m)\cos(\omega t)]\ge l_{r,s}\). To estimate \(E[(V-V_0)\cos(\omega t)]\), add \(4B_M/(\delta' T)\) to \(h_{r,s}\), with \(\delta'=.25+\log\sqrt{Qt_0/(2\pi)}-\log R\). If \(\delta'\le0\) omit the frequency. In fact the active short product has \(\log(Qt/(2\pi k))\ge.25+\log\max(X,Y)\) and both orientations then have derivative at least \(\delta'\). Denote this amended upper bound by \(h'_{r,s}\).

For \(r\le J\) the reduced positive frequencies are distinct; their spacing is at least \(1/(J^2+1)\) by comparing the integer cross products. The same bound holds for each sum of two frequencies and for twice a frequency. Integration of the cosines on \([0,T]\) gives
\[
 EP^2\le \tfrac12\sum p_{r,s}^2+
            2(J^2+1)(\sum p_{r,s})^2/T .
\]
This full interval is used even though the main polynomials vanish below \(t_0\). Thus one may deduct
\[
 I_P=2\sum p_{r,s}l_{r,s}-\tfrac12\sum p_{r,s}^2-
            2(J^2+1)(\sum p_{r,s})^2/T
\]
from the raw upper variance of \(S-m\) by replacing it with \(S-m-P\). In return one adds \(E[P(V-V_0)]\le\sum p_{r,s}h'_{r,s}\) to the covariance. Cauchy–Schwarz and restoration of the AFE errors now follow exactly as in [the first projection](INTERFERENCE.md). Positive deductions use the upper slab denominator \((U+b)^4\), and positive costs the lower \(U^4\). The [finite polynomial selection](twisted.py) takes \(p_{r,s}=2(l_{r,s}-\kappa h'_{r,s})_+\) with a positive scalar \(\kappa\) chosen from the preceding variance upper bounds; the inequality is valid for every such selection.

The middle comparison printed by the script uses a separate option with two asymmetric AFEs and \(J=70\). The certified default and final column use the stationary integral and \(J=512\).

~~~powershell
python -B round8/critical/rational_fourth.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. The signed rational stationary contribution, boundary estimates and joint projection are by Codex.
