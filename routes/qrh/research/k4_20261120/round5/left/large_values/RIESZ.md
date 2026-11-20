# A finite signed Riesz detector

This is an auxiliary conditional result for the [finite density box](GAUSSIAN.md). All assumptions, and the sharp \(Q=210,N=32768\) polynomial \(P\), are as in that proof. Let \(d=\beta-\frac12,\ D=3/8,\ \lambda=2D=3/4\). For \(Y=c_YT\) define the *finite* polynomial
\[
 D_Y^{\rm R}(z)=\sum_{N<n\le Y}a(n)n^{-z}(1-(n/Y)^\lambda).
\]
Its Mellin kernel \(K(w)=\lambda/(w(w+\lambda))\) is the difference \(1/w-1/(w+\lambda)\). Shifting as in GAUSSIAN.md gives
\[
 1-Y^{-\lambda}+D_Y^{\rm R}(\rho)
 =P(1)Y^{1-\rho}K(1-\rho)+I_\rho^{\rm R},
 \quad I_\rho^{\rm R}=\frac{Y^{-d}}{2\pi}\int_{\mathbb R}
 (\zeta P)(1/2+i(\gamma+v))K(-d+iv)Y^{iv}\,dv.
\]
The kernel pole \(-\lambda\) is to the left of the new contour. On the horizontal contour segments for each fixed \(\rho\), Euler summation bounds \(\zeta(s)\) by \(O(\sqrt{|\Im s|})\) uniformly for \(\Re s\ge1/2\) in this fixed strip. The inverse Mellin integral and its shift converge. The pole on the right has modulus less than \(10^{-9}\) by \(H>3\cdot10^{12}\), \(Y\le512e^{45}\), \(\beta>.8\), and \(|P(1)|\le210N\). Also \(Y^{-\lambda}<10^{-9}\). Thus \(|I_\rho^{\rm R}|<1/2\) implies \(\Re D_Y^{\rm R}(\rho)<-.4999\).

Set \(B=\min(.9H,T/200)\), ensuring \(H-B>0\). The far integral is less than \(10^{-4}\) in modulus because
\[
 \frac{6\lambda R_P}{\pi}Y^{-d}
 \left(\frac{\sqrt{T+1}}B+\frac2{\sqrt B}\right)<10^{-4},\qquad
 R_P=\sum_{n\in\mathcal D}n^{-1/2}<431.
\]
Here \(0<1/|(-d+iv)(\lambda-d+iv)|\le v^{-2}\), and \(|\zeta(1/2+it)|\le6\sqrt{|t|+1}\). The script checks the estimate uniformly by \(d\ge.3,\ 32\le c_Y\) and \(H\le T\le e^{45}\).

With \(c=2s-\tfrac12,\ a=c-\beta\), the same Cauchy estimate with \(P_a(v)\) as before is bounded by \(J_sY^{1-2s}\int_{-B}^B P_a(v)|\zeta P|^2\,dv\), now with
\[
 J_s=\frac{\lambda^2}{4\pi(c-\Theta)(\lambda-D)} .
\]
Indeed the squared kernel divided by \(P_a\) is at most \(\lambda^2/[a((\lambda-d)^2+v^2)]\). The ordinates \(t\) used in the sum of Poisson kernels satisfy \(0.1H\le t\le1.005T\). Accordingly use the previous \(F_s\) with additive slack .004 in place of .001 and replace \(T\log T\) by at most \(1.0053T\log T\).

The optional reflection improvement uses both equal-ordinate zeros \(\beta+i\gamma,1-\beta+i\gamma\) in the Poisson sum. Write \(C=c-\frac12,\ a=C-d,\ \tilde a=C+d\). Then \((d^2+v^2)(P_a(v)+P_{\tilde a}(v))\ge2C/3\) in the box. With positive denominators removed, this is the nonnegativity of
\((C^2-d^2)(4d^2-C^2)+(C^2-2d^2)v^2+2v^4\),
since \(C/2\le d\le3/8\) and \(C\ge.6\). Every reflected mate occurs at most once. This replaces \(1/(c-\Theta)\) in \(J_s\) by \(3/(2C)\). The normalization is shared with the separately audited reflected Gaussian estimate.

| \(c_Y\) | Full-box Type II fraction, single Poisson kernel | Full-box fraction with reflection | Reflected fraction at \(s=.85,\ T=e^{35}\) |
|---:|---:|---:|---:|
| 32 | <.77062 | <.53697 | <.37080 |
| 128 | <.30512 | <.20257 | <.14051 |
| 512 | <.12671 | <.07911 | <.05325 |

Fractions use the [original target](../../spectrum/DENSITY_TARGET.md) \(7(\log T)T^{p_s}\). For example a bound \(6.44(\log T)T^{p_s}\) on zeros with \(\Re D^{\rm R}_{512T}(\rho)<-.4999\) would finish that target. This signed estimate is still open.

For the matched ideal Poisson weight \(a=d\), the Cauchy cost for a compact cutoff with derivative profile \(h(t)\) on the variable \(t=\log(Y/n)\ge0\) is proportional by Plancherel to \(\int_0^\infty |e^{dt}h(t)|^2dt\). If \(\int_0^\infty h=1\), Cauchy–Schwarz bounds this last integral below by \(2d\), attained at \(h(t)=2d e^{-2dt}\). This explains the Riesz cutoff with \(\lambda=2d\) and the uniform selection \(2D\). The statement concerns this matched one-sided Cauchy cost.

Run **python -B riesz.py**. This work is attributed jointly to Claude and Codex following the repository protocol; Codex derived this finite cutoff analysis.
