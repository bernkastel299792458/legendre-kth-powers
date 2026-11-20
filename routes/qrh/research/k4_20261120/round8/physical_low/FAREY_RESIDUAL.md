# Exact Ramanujan aggregation inside the four-sided remaining band

Here \(x=e^{116}\), the unit wheel \(Q\) is squarefree, and \(G=G_Q(z)\), \(P_0,F,X,X_-,Y,q_0,m\) are as in [the physical proof](PHYSICAL_L2.md). Put \(\rho(n)=n/\varphi(n)\). For the \(Q=23\#,\ Y=e^{75},\ q_0=X/200\) example below, the remaining additive frequency may be restricted to \(2<\kappa\le 2.5\cdot10^{17}\). This note gives an exact cancellation on a genuine subset of this residual. The contribution from the complementary terms is open.

## Retaining the original modulus and both frequency cutoffs

Write \(e(v)=e^{2\pi i v}\), \(\widehat F(\xi)=\int F(t)e(\xi t)\,dt\), \(c_Q(h)=\sum_{v\bmod Q,(v,Q)=1}e(vh/Q)\). The Selberg coefficients have the exact representation
\[
 G\lambda_d=\mu(d)d\sum_{\substack{m\le z,\ d\mid m\\(m,Q)=1}}
          \frac{\mu^2(m)}{\varphi(m)},\qquad
 G\sum_{d\mid n}\lambda_d=
 \sum_{\substack{m\le z\\(m,Q)=1}}\frac{\mu(m)c_m(n)}{\varphi(m)}.
\]
For the signed band, exchange the two Selberg numerators with the original divisor sums **before** dropping any of their restrictions. Fix the squarefree integers \(m=gu,\ r=gv\); \(g,u,v\) are then pairwise coprime, unit to \(Q\), and \(l=[m,r]=guv\). The original integers are \(d\mid m,\ e'\mid r,\ q=[d,e']\). An original positive harmonic \(j\) at \(j/(Qq)\) supplies the common harmonic \(h=j l/q\) at \(h/(Ql)\). Since \(l\) is a \(Q\)-unit, \(c_Q(j)=c_Q(h)\). In particular the true \(\kappa=hX/(Ql)\) is unchanged.

For each fixed \(m,r,h\) the normalized multiplier in the original residual is precisely
\[
 \frac{2P_0 c_Q(h)}{Q G^2\varphi(m)\varphi(r)}
 C_{m,r}(h;Y,q_0)\,\widehat F(h/(Ql)),\qquad
 C_{m,r}=\sum_{\substack{s\mid(l,h)\\Y<l/s\le q_0}}
   \mu\left(\frac{uv}{(s,uv)}\right)
   \prod_{\substack{p\mid g\\p\nmid s}}(p-2).
\]
Take real parts after summing and impose precisely the original bounds on \(\kappa\). Indeed the raw multiplicity for each \(d,e'\) is \(\mu(d)\mu(e')(d,e')\) from \(de'/q\). Set \(s=l/q\). A prime of \(s\) occurs on neither side. For \(p\mid uv,\ p\nmid s\) its unique side must be chosen, giving \(-1\). For \(p\mid g,\ p\nmid s\) there are two one-sided choices and one bilateral choice, whose signed weights are \(-1,-1,p\). Multiplication gives the formula with every endpoint unchanged. All exchanges on a finite \(\kappa\)-band are finite.

Without modulus restriction the factor is
\[
 \mu(uv){\bf1}_{(h,uv)=1}
        \prod_{p\mid g}(p-2+{\bf1}_{p\mid h}).
\]
The unrestricted uniform term \(h=0\) has \(u=v=1\); the remaining sum yields exactly \(\eta_Q/G\), since \(c_Q(0)/Q=\eta_Q\) and the multiplicity is \(\varphi(g)\). Within the actual residual the unrestricted factor is already exact whenever \(l\le q_0,\ l/h>Y\). Indeed all divisors of \((l,h)\) are at most \(h\); thus every \(q=l/s\) then lies between the required modulus endpoints. For \(l>q_0\) the lower bound on \(s\), and for \(l/h\le Y\) its upper bound, must be retained.

## Quantifying a cancellation on actual frequencies

Take the first prime \(p\nmid Q\). Put \(B=z/\sqrt m,\ A=B/\sqrt2\), using \(m\) here for the physical cutoff. Consider \(g=1,\ A<u,v\le B,\ u=pw\); \(w,v\) are squarefree, coprime to each other and to \(Qp\). For every positive \(h\) divisible by \(p\) in
\[
     \lfloor k_0 Q/m\rfloor<h\le \lfloor 4000Q/m\rfloor
\]
the verifier checks \(k_0<hX/(Q uv)<8001,\ uv\le q_0,\ uv/h>Y\). Thus all the summands of \(C_{u,v}(h)\) are retained, and this entire coefficient vanishes exactly by \(p\mid (h,u)\). In particular \(s=1\) and \(s=p\) are two distinct raw terms with opposite unit coefficients, at the *same frequency*. This remains true if other primes of \(h\) divide \(uv\). An independent finite-integer enumeration in the program also compares the compressed and raw formulas at small cutoffs and at both modulus boundaries.

For a quantitative lower bound on the price of taking moduli too early, set \(\eta'=\varphi(Qp)/(Qp),D=2^{\omega(Qp)},\ d_1=(B-A)/p,\ d_2=B-A\). Starting from at least \((\eta'd_1-D)(\eta'd_2-D)\) ordered unit pairs, subtract the candidates with a prime square in either row or a mutual prime. For \(R=\sum_{\ell\nmid Qp,\ \ell\ {\rm prime}}\ell^{-2}\) these three upper counts are
\[
 (d_1R+\sqrt{B/p})(\eta'd_2+D),\quad
 (d_2R+\sqrt B)(\eta'd_1+D),\quad
 d_1d_2R+(d_1+d_2)(1+\log B)+B/p.
\]
For instance the final expression sums \((d_1/\ell+1)(d_2/\ell+1)\) for \(\ell\le B/p\). The bound on \(R\) takes all allowed primes through 2000 plus \(1/2000\). The surviving count divided by \(B^2\) lower-bounds the actual \(\sum1/[\varphi(u)\varphi(v)]\) on these pairs. Denote this lower by \(J\).

All contributing \(t\) lie strictly between \(X_-\) and \(X\), so the real part of \(e(-\xi X)\widehat F(\xi)\) is at least \(\cos(2\pi\kappa_{\max}(1-X_-/X))\int F\). The cosine is positive on the whole tested range. The original log weight has integral \(A_{\rm leak}=I(1-a/\pi)\) on the full line by its [exact spectrum](PHYSICAL_L2.md). Its omitted tails have integral at most \(4/[U(1-(a/U)^2)]\), \(U=Hr\). Because \(F\) majorizes the retained original weight, the value of \(P_0|\widehat F|\) is at least
\[
 V=u_0 e^{-2r}
 \left(A_{\rm leak}-4/[U(1-(a/U)^2)]\right)
 \cos(2\pi\kappa_{\max}(1-X_-/X)),\qquad
 u_0=(c+2r)e^r/I .
\]
Consequently the original **sum of absolute complex amplitudes** on just the two raw terms per triple \(u,v,h\), including the Fourier normalization for the two frequency signs, exceeds
\[
 \frac{4V J}{Q G_+^2}\sum_{h_{\min}\le h\le h_{\max},\,p\mid h}|c_Q(h)|.
\]
The sum is exact by \(c_Q(pj)=c_Q(j)\) and integer divisor inversion. \(G_+\) is the convolution upper denominator. The signed contribution of the *entire compressed group* is zero. These figures do not supply a refund against a previously proved signed bound on some other decomposition.

| \(Q,m,\log Y,k_0\) | Prime | Upper \(\kappa\) | Raw absolute mass strictly above | Compressed signed mass |
|---|---:|---:|---:|---:|
|223092870, 200, 75, 2|29|8000.039|.00584418207|0|
|6469693230, 337, 74, 1|31|8000.039|.00620320797|0|
|7420738134810, 431, 70.7, 1|41|8000.039|.01131163125|0|

~~~powershell
python -B round8/physical_low/farey_residual.py --Q 223092870 --cut 200 --logY 75 --minimum 2 --integer-check --lower .00584418207
python -B round8/physical_low/farey_residual.py --Q 6469693230 --cut 337 --logY 74 --lower .00620320797
python -B round8/physical_low/farey_residual.py --Q 7420738134810 --cut 431 --logY 70.7 --lower .01131163125
~~~

## The real-part cancellation with the true physical center

For the same family there is a lower bound on the sum of the absolute values of the actual real parts. This matters because the residual eventually takes a real part. Set \(C=e^c,\ w=.0002,\ U_0=1000\), and write \(M_0=u_0 e^{-2r}(A_{\rm leak}-4/[U(1-(a/U)^2)])\). With \(\xi=h/(Q uv)\), one has
\[
 |P_0\widehat F(\xi)-e(\xi C)P_0\!\int F|\le E,\qquad
 E=u_0\left(4w e^{116-c}S_0+
 e^r\left[2\pi\kappa_{\max}(\exp(U_0/H)-1)A_{\rm leak}
 +\frac{8}{U_0(1-(a/U_0)^2)}\right]\right).
\]
Indeed \(F-W\ge0\) and its total mass under \(P_0\) is at most \(2u_0 w e^{116-c}S_0\) by superlevel dilation. The error from this increment is at most twice its mass. On the original \(|H\log(t/C)|\le U_0\), the Lipschitz inequality for \(e(\xi t)\) gives the first term inside the square brackets since \(C\le X\). In the exterior the phase difference is at most two and the log-area is at most \(4/[U_0(1-(a/U_0)^2)]\). The physical Jacobian in both original regions contributes at most \(e^r\). In particular
\[
 P_0|\Re\widehat F(\xi)|\ge M_0|\cos(2\pi \xi C)|-E .
\]

For \(h=pj,\ j_0<j\le j_1\), put \(\alpha=pC/(Q uv)\). The coefficients \(a_d=\prod_{\ell\mid d}(\ell-2)\) satisfy \(|c_Q(j)|=\sum_{d\mid(Q,j)}a_d\). For every \(\alpha\) and positive integer \(N\),
\[
 \sum_{k=1}^N\cos^2(2\pi\alpha dk)\ge N/4-3/8.
\]
Fold \(2\pi\alpha d\) to \(v\in[0,\pi/2]\) without changing any square. At \(v>0\) the sum equals \(N/2-1/4+\sin((2N+1)v)/(4\sin v)\). If its sine numerator is negative then \(v\ge\pi/(2N+1)\), so \(\sin v\ge2/(2N+1)\), giving the asserted bound. The case \(v=0\) is immediate. Since \(|\cos|\ge\cos^2\), the real weight on the required interval is at least
\[
 J_{\rm re}=\sum_{d\mid Q}a_d
 \max\left(0,\frac{\lfloor j_1/d\rfloor}{4}-\frac38-\lfloor j_0/d\rfloor\right).
\]
With \(N_Q=\sum_{j_0<j\le j_1}|c_Q(j)|\), the raw absolute real price including both opposite terms is at least \(4J(M_0 J_{\rm re}-E N_Q)/(QG_+^2)\). Their signed sum is exactly zero. In particular each of the two real positive and negative parts on these pairs equals one half of the raw absolute real price.

| \(Q,m,\log Y,k_0\) | Lower bound for the raw absolute real price |
|---|---:|
|223092870, 200, 75, 2|.0014348839024|
|6469693230, 337, 74, 1|.0015254033484|
|7420738134810, 431, 70.7, 1|.0027866178516|

~~~powershell
python -B round8/physical_low/farey_residual.py --Q 223092870 --cut 200 --logY 75 --minimum 2 --integer-check --lower .00584418207 --real-lower .0014348839024
python -B round8/physical_low/farey_residual.py --Q 6469693230 --cut 337 --logY 74 --lower .00620320797 --real-lower .0015254033484
python -B round8/physical_low/farey_residual.py --Q 7420738134810 --cut 431 --logY 70.7 --lower .01131163125 --real-lower .0027866178516
~~~

## A broad subband and the exact form of its two boundaries

The center estimate just proved also supplies \(P_0|\widehat F(\xi)|\ge M_0-E\), even when the full physical support spans many turns of the phase. Both this bound and the real bound hold with any \(a<U_0<Hr\), using that same \(U_0\) throughout. The verifier uses the sharper elementary estimate
\[
 \sum_{k\le N}\cos^2(kv)\ \ge\ 3N/8-7/16 .
\]
For \(0<v\le\pi/2\), \(0\le\csc v-1/v\le \pi v/12<1/2\) follows from \(v-\sin v\le v^3/6\) and \(\sin v\ge2v/\pi\). Also \(\sin x\ge-x/4\) for \(x\ge0\). On \([\pi,4]\) this follows from \(\sin x\ge\pi-x\ge-x/4\), and outside that interval either the sine is nonnegative or \(x\ge4\). Thus when the sine numerator of the exact identity is negative it satisfies \(\sin((2N+1)v)/\sin v\ge-(2N+1)/4-1/2\), proving the estimate. The earlier real calculation remains valid with its original quoted lower bounds.

The table uses the same subset of \(u,v\), extends its \(h\) limit to \(\lfloor b Q/m\rfloor\), and gives strict lower bounds. For every term, \(\kappa<2.001 b,\ k_0<\kappa,\ Y<uv/h\), and \(uv<X/m\), as verified with ball arithmetic. Expansion of the positive Selberg numerators may subdivide a fixed original \((d,e',j)\) repeatedly across \(u,v\), but all subdivisions have the same sign and phase for that original triple. Thus their absolute real prices add. The sign cancellations shown here occur before any estimate for the remaining pairs or other phases.

| \(Q,m,\log Y,k_0\) | \(b\) | \(U_0\) | Absolute real | Absolute complex | Actual signed |
|---|---:|---:|---:|---:|---:|
|223092870,200,75,2|450000000|64|91.08266|511.17080|0|
|6469693230,337,74,1|128000000|120|50.12018|176.92380|0|
|7420738134810,431,70.7,1|3100000|780|3.17495|8.77082|0|

~~~powershell
python -B round8/physical_low/farey_residual.py --Q 223092870 --cut 200 --logY 75 --minimum 2 --stop 450000000 --core 64 --integer-check --lower 511.17080 --real-lower 91.08266
python -B round8/physical_low/farey_residual.py --Q 6469693230 --cut 337 --logY 74 --stop 128000000 --core 120 --lower 176.92380 --real-lower 50.12018
python -B round8/physical_low/farey_residual.py --Q 7420738134810 --cut 431 --logY 70.7 --stop 3100000 --core 780 --lower 8.77082 --real-lower 3.17495
~~~

There is also an exact classification across *all* source pairs on the open subband \(\kappa<X/(QY)\). Here \(l/h=X/(Q\kappa)>Y\), so \(l/s>Y\) for every \(s\mid(l,h)\). Put \(A_s=\mu(uv/(s,uv))\prod_{p\mid g,\,p\nmid s}(p-2)\) for such \(s\). With \(C^{\rm full}\) the unrestricted multiplier displayed above, the complete original coefficient is
\[
 C=C^{\rm full}-\sum_{\substack{s\mid(l,h)\\s<l/q_0}}A_s,
\]
The upper equality \(l/s=q_0\) stays in the original coefficient. Since \(l=guv\le z^2/g\), \(q_0=X/m\), and \(z^2<X\), every correction satisfies \(gs<m\). For all three wheels the square of the smallest unit prime exceeds \(m\). Therefore when \(l>q_0\) there are exactly two possibilities for its corrections:

* \(g=1\). The correction is \(A_1+\sum_{p\mid(l,h),\,p<l/q_0}A_p=\mu(uv)(1-\#\{p\mid(l,h):p<l/q_0\})\).
* \(g=P\) a single prime unit with \(P<m\). The correction is \(A_1=\mu(uv)(P-2)\).

For \(l\le q_0\) there is no correction. These cases include the unbounded range of \(h\) allowed by the subband. For \(Q=23\#,29\#,37\#\), respectively, the subband extends at least to \(2.8680\,10^9,\ 2.6883\,10^8,\ 6.3546\,10^6\). At \(\kappa=X/(QY)\) a term with \(s=h\) would hit the excluded lower endpoint and must be tested by the original four-sided formula.

2026-11-20. Joint project attribution to Claude and Codex.
