# Removing a complete nonstationary product from the fourth moment

Let \(u=\log T\). For \(Q=210,\alpha=1,w=.04,Z=384\), the constants below bound
\[
 \frac1{T u^4}\int_0^T|\zeta(1/2+it)E_{210}(1/2+it)|^4\,dt
\]
for every \(u\ge U\). The same [approximate functional equation](../../round6/phase/SMOOTH_PHASE.md), including its elementary phase and remainder, is used throughout.

| \(U\) | Previous centered bound | Same slabs, no product removed | Fixed \(M=10^6\) | Moving cutoff |
|---:|---:|---:|---:|---:|
|35|.001260749|.001258945|.001238933|.001207338|
|37|.001106399|.001104903|.001089126|.001056038|
|40|.000954756|.000953590|.000942148|.000907721|

## The short product and the signed cubic terms

Take the two sharp polynomials \(A,B\) on a paired cutoff and include \(Q^{-1/2}\) in \(B\). Their lengths are \(X(t),Y(t)\), proportional to \(\sqrt{t}\), with \(X(t)Y(t)=Qt/(2\pi)\). Set \(\ell=\sqrt{Q/(2\pi)}e^{-w}\min(\alpha,\alpha^{-1})\), so both lengths are at least \(\ell\sqrt t\). In the conjugated convention let
\[
 W=e^{i\phi}AB,\qquad V=2\Re W,\qquad S=|A|^2+|B|^2,\qquad
 \phi=t\log(Qt/(2\pi e))-\pi/4 .
\]
Expectations use \(dt/T\) and the paired cutoff average. The original polynomials vanish before the AFE starts at \(t_0\).

For \(k\le M\), let \(k_1\) be the part of \(k\) coprime to \(Q\), and put
\[
 b_k=\frac{c_Q(k)\tau(k_1)}{\sqrt Q},\qquad
 t_k=\max(t_0,e^{2\delta}k^2/\ell^2).
\]
Thus \(b_k/\sqrt k\) is the exact coefficient after collecting all products of a forward and a dual index with product \(k\). For every eligible forward divisor \(d\) one has \((d,Q)=1\) and \(c_Q(k/d)=c_Q(k)\), so all summands at the same \(k\) have the same sign. Define
\[
 W_0(t)=e^{i\phi(t)}\sum_{\substack{k\le M\\t\ge t_k}} b_k k^{-1/2-it},
 \qquad V_0=2\Re W_0 .
\]
On this support \(k\le e^{-\delta}\min(X,Y)\). Hence all its factor pairs really occur in \(W\). The fixed-cutoff variant replaces all \(t_k\) by \(t_M\), which preserves this property.

For every term of \(S W_0\), the derivative of its phase is at least
\[
 \log\frac{Qt}{2\pi k}-\log\max(X(t),Y(t))
 =\log\frac{\min(X(t),Y(t))}{k}\ge\delta .
\]
This includes both signs of the frequency in each of \(|A|^2,|B|^2\). For \(WW_0\), since a product from \(W\) is at most \(Qt/(2\pi)\), the derivative is at least \(\log(Qt/(2\pi k))\ge\delta\). For \(W_0^2\) the lower bound is \(2\delta\). For \(W_0\) it is \(\delta\). These derivatives are increasing, and each term is active on a single interval. One integration by parts bounds a phase integral with increasing derivative at least \(d>0\) by \(2/d\). This treats the indicated subsets of both signed terms \(|A|^2\Re W\) and \(|B|^2\Re W\) before applying Cauchy–Schwarz to the remainder.

## Removing the energy

Write \(D_J=\sum_{k\le J}b_k^2/k,\ B_J=\sum_{k\le J}|b_k|/\sqrt k\), and
\[
 D_*=\sum_{k\le M}\frac{b_k^2}{k}(1-t_k/T)_+ .
\]
Let \(L_f,L_d\) bound the sums of the absolute forward and dual coefficients at \(T\), including the inverse square roots and dual scaling. For each periodic raw absolute sequence with mean \(\rho\) and interval discrepancy \(D\), the decreasing weight gives \(2\rho\sqrt{X_{\max}}+D\), using [the periodic discrepancy](../../round6/phase/SMOOTH_PHASE.md). Divide the dual bound by \(\sqrt Q\).

In \(E(W\overline W_0)\), equal products contribute exactly \(D_*\). For a different product \(i\) against \(k\), its logarithmic frequency gives an absolute integral at most \(2/|\log(i/k)|\). For \(i\le2M\) use \(1/|\log(i/k)|\le2M/|i-k|\). At each fixed nonzero shift, Cauchy bounds the sum of amplitudes by \(\sqrt{D_{2M}D_M}\), including incomplete factor pairs by the same-sign observation. Summing both orientations costs \(2(1+\log(2M))\). For \(i>2M\) the frequency gap is at least \(\log2\). It follows that
\[
 |E(W\overline W_0)-D_*|\le e_c+e_f,\quad
 e_c=\frac{8M(1+\log(2M))\sqrt{D_MD_{2M}}}T,\qquad
 e_f=\frac{2L_fL_d B_M}{T\log2}.
\]
The same calculation with both products at most \(M\) gives \(E|W_0|^2\le D_*+e_0,\ e_0=4M(1+\log M)D_M/T\). The preceding nonstationary bounds give
\[
 |E WW_0|\le e_h=\frac{2L_fL_d B_M}{\delta T},\qquad
 |E W_0^2|\le e_s=\frac{B_M^2}{\delta T},\qquad
 |E S V_0|\le e_P=\frac{4B_M(L_f^2+L_d^2)}{\delta T},\qquad
 |E V_0|\le e_m=\frac{4 B_M}{\delta T}.
\]
Expanding \(V V_0\) gives \(2\Re(W\overline W_0+WW_0)\), and \(V_0^2=2|W_0|^2+2\Re W_0^2\). Consequently
\[
 E(V-V_0)^2\le EV^2-\Delta,\qquad
 \Delta=2D_*-4(e_c+e_f+e_h)-2(e_0+e_s).
\]
Fix the integer \(M\) from the lower endpoint \(T_0=e^U\) of a slab. Then \(D_*\) increases with \(T\) while all the displayed error bounds decrease: \(L_f,L_d\) have the form \(aT^{1/4}+b\) with \(a,b\ge0\). Each quantity may thus be bounded at \(T_0\). For the moving calculation choose \(\delta=.25\) and an integer near \(e^{-\delta}\ell\sqrt{T_0}\); the proof admits **any** fixed \(M\). The fixed calculation uses \(\delta=1\).

## Integer energy for the moving cutoff

Factor \(k=d n\) with \(d\) supported on the primes of \(Q\) and \((n,Q)=1\). Then \(b_k^2=c_Q(d)^2\tau(n)^2/Q\). The positive convolution identity \(\tau^2=1*1*1*\mu^2\) follows prime by prime: the generating function is \((1+x)/(1-x)^3=\sum_{r\ge0}(r+1)^2x^r\).

Replacing \(\mu^2\) by \(1\) gives a positive upper measure for \(D_M,D_{2M}\). For the decreasing nonnegative test \(F(k)=\mathbf1_{k\le M}(1-t_k/T)_+\), the loss in this replacement is at most the total relaxed mass times \(\sum_{p\nmid Q}p^{-2}\). Indeed, in the fourth unit factor write \(n_4=p^2n_4'\), and use \(F(p^2k')\le F(k')\); the harmonic coefficient contributes \(p^{-2}\). All primes in this sum are coprime to \(Q\). The [energy calculation](product_energy.py) sums those primes to 2000 and adds \(1/2000\). Use \(B_M\le\sqrt{M D_M}\).

The positive relaxed measure is evaluated on the grid \(b^i,\ b=2^{1/48}\). The factor \(1\) has grid index zero; an integer \(a>1\) has index \(i\) when \(b^{i-1}<a\le b^i\). A positive mass at total index \(i\) in the fivefold convolution has integer product at most \(\lfloor b^i\rfloor\) and at least \(b^{\max(0,i-5)}\), allowing equality at one. The four unit masses in each bin are computed from
\[
 \sum_{\substack{n\le N\\(n,Q)=1}}\frac1n
 =\sum_{e\mid Q}\frac{\mu(e)}e H_{\lfloor N/e\rfloor},
 \qquad H_l=\psi(l+1)+\gamma\quad(l\ge1),\quad H_0=0 .
\]
The fifth measure enumerates every \(Q\)-smooth \(d\le2M\) with weight \(c_Q(d)^2/(Qd)\). Larger \(d\) cannot affect the desired sums. Multiplying the polynomials in Arb gives the bin weights. For the lower bound retain \(\lfloor b^i\rfloor\le M\) and evaluate \(F\) at that upper integer before the squarefree correction. The upper sums retain any bin with \(\lfloor b^{\max(0,i-5)}\rfloor\le M\) or \(2M\), respectively. Forms with product at most \(2M\) have total index less than \(\log_b(2M)+5\), apart from the exact unit at zero; the array extends six bins beyond the ceiling. All nonintegral grid endpoints are floored in interval arithmetic, and exact powers of two are handled as integers.

For the fixed \(M=10^6\) comparison the verifier instead enumerates the exact integer \(\tau(k_1)\) by sieving all divisors coprime to \(Q\) for every \(k\le2M\). Interval endpoint weights bound the sums on positive integer blocks of relative width at most \(1/256\), and a checked bound excludes integer-sum overflow.

## Uniform fourth coefficient

Use the published project inputs \(ES^2\le a u^4,\ EV^2\le c u^4,\ ES\ge m\ge0,\ |EV|\le h\) in the [centered phase calculation](../../round6/phase/CENTERED_PHASE.md). On a slab \(U\le u\le U+b\), write
\[
 E SV=E[(S-m)(V-V_0)]+mEV+E[(S-m)V_0].
\]
For a nonnegative certified \(\Delta\), Cauchy–Schwarz here gives
\[
 \frac{E(S+V)^2}{u^4}\le a+c+
 2\sqrt{\{a-m^2/(U+b)^4\}_+
         \{c-\Delta/(U+b)^4\}_+}
 +\frac{2(mh+e_P+m e_m)}{U^4}.
\]
The verifier takes the minimum with the prior estimate, then restores all actual AFE and early-height terms. The [implementation](interference.py) imports the original fourth-moment function into a private namespace and changes just the indicated scalar covariance expression, asserting that it occurs exactly once. By default it takes three adjacent slabs of width one followed by the prior uniform half-line starting at \(U+3\). Setting \(M=0\) tests the same subdivision with its original covariance formula. All other numerical inputs and the definition of the underlying \(\zeta E_Q\) are shared among the comparison columns.

~~~powershell
python -B round8/critical/interference.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. The nonstationary product and complete energy subtraction are by Codex.
