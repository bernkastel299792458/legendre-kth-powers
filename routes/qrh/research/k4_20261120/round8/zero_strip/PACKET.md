# A signed Gaussian pair condition in the second rectangle

Assume QRH(7/8). Write \(\Theta=7/8,\ s=.865,\ H=3000175332800,\ T=H e^{7/4}\). Ordinates and submultisets carry multiplicity. Among zeros \(\beta>s,\ H<\gamma\le T\), at most 178614 lack a neighbor of real part \(>.75\), at a distinct ordinate within distance 2, with negative Gaussian inner product in the sense of (1). The analogous cap for \(\beta'>.78\) within 1.5 is 352421. No restrictions on the real parts of the remaining zeta zeros beyond QRH are imposed. Neighbors may lie outside the height endpoints. This is a condition on the local configuration of any counterexample to the target count 420070. A clustered configuration can satisfy it.

## The complex packet

Take \(v,U>0\), put \(k(a)=\exp(-Ua+v^2a^2/2),\ M=\sqrt{2\pi}v,\ d_0=\sqrt\pi/v\). For a zero with \(a_i=\Theta-\beta_i\), use
\[
 g_i(t)=k(a_i)e^{-v^2(t-\gamma_i)^2/2}
             e^{i(U-a_iv^2)(\gamma_i-t)}.
\]
Completing the square on the real line gives
\[
 d_0^{-1}\Re\langle g_i,g_j\rangle =
 \Omega_{ij}=k(a_i)k(a_j)
 e^{-v^2[(\gamma_i-\gamma_j)^2+(a_i-a_j)^2]/4}
 \cos\big[(U-(a_i+a_j)v^2/2)(\gamma_i-\gamma_j)\big].                 \tag{1}
\]

Use the explicit formula in the Fourier convention \(h_t(z)=\int e^{i(z-t)u} e^{-(\Theta-1/2)u}e^{-(u-U)^2/(2v^2)}du\). At \(z=(\rho_i-1/2)/i\) it is \(M g_i(t)\). The function is entire and decays as a Gaussian on every fixed horizontal strip. Its even part suffices in the formula by the symmetry \(z\mapsto-z\), including for the poles and prime terms. Complex linearity allows this complex test. The term coming from positive log frequencies is a one-sided complex Dirichlet series. [Chirre and Gonçalves, Proposition 5](https://doi.org/10.1007/s00209-021-02820-9)

Define
\[
 P(t)=-M^{-1}\sum_{n\ {\rm odd}}\Lambda(n)n^{-\Theta}e^{-(\log n-U)^2/(2v^2)}e^{-it\log n}.
\]
On \(J=[H-b,T+b]\), put \(E=P-\sum_{\rho}g_\rho\). Then
\[
 \|E\|_\infty\le [k(\Theta)+k(\Theta-1)]e^{-v^2(H-b)^2/2}
 +\frac{k(\Theta-1/2)}{2\pi}\left[\frac{\sqrt{2\pi}}v(\log(T+b+4)+6)+\frac2{v^2}\right]
 +\frac{3e^{-U^2/(2v^2)}+\log2\,k(\Theta)(1+\sqrt{2\pi}v/\log 2)}M.    \tag{2}
\]
The first term bounds both poles. The archimedean term uses \(|\Re\psi(1/4+ix/2)-\log\pi|\le\log(T+b+4)+6+|x-t|\), from the Euler integral comparison \(|\psi(z)-\log z|\le 1/\Re z\) for \(\Re z>0\). For \(|z|\le1\) use \(|\log|z||\le\log4\) and \(T>e^{29}\); otherwise \(\log|z|\le\log(T+b+4)+|x-t|\). The negative-frequency prime series is bounded by \(3e^{-U^2/(2v^2)}\) as \(U/v^2\ge2\), by \(\sum_{n\ge2}\log n/n^2<3\). Complete the square at \(u=U-\Theta v^2\) for the even prime powers and bound the unimodal lattice sum by its maximum plus its full integral divided by \(\log2\).

## An upper bound on the arithmetic energy

For \(j=0,1\) put \(S_j=\sum_n\Lambda(n)^2 n^{j-2\Theta}e^{-(\log n-U)^2/v^2}\). On an interval \(J\), the two-endpoint Montgomery–Vaughan inequality gives
\[
 M^2\int_J |P|^2 \le (|J|+4.2)S_0+4.2 S_1.
\]
The nearest gap on the odd integers is at least \(\log(1+2/n)\ge2/(n+1)\); the two Hilbert forms cost \(2(4\pi/3)\) before inserting this gap. Truncation followed by absolute convergence gives the infinite version. [Project statement and source of the Hilbert inequality](../../round7/qrh_strip/INCREMENT.md)

Here are the details of the upper bound returned by the shared function prime_energy. With \(X=e^{16},\ \epsilon=.002\), one has \(|\psi(x)-x|\le\epsilon x\) above \(X\): Dusart's \(|\theta-x|\le.2x/\log^2x\) above 3594641, together with \(\theta(x)\le1.01624x\), gives error at most \(.2/16^2+1.01624[e^{-8}+(16/\log 2)e^{-32/3}]\) there; each term decreases. Below \(X\) use \(\psi(x)<1.04x\). [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442) [Rosser and Schoenfeld, Theorem 12](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

Put \(f(x)=(\log x)x^{j-2\Theta}e^{-(\log x-U)^2/v^2}\). Since \(\Lambda(n)^2\le(\log n)\Lambda(n)\), \(S_j\le\int f\,d\psi\). The logarithmic derivative is positive up to \(X\) for these rows. Bound the early contribution by \(1.04X f(X)\). Integration by parts on the tail costs at most \(\epsilon(\int f\,dx+3\max xf)\) in addition to the ordinary integral, since \(xf\) is unimodal on \(x\ge1\) and \(x|f'|\le|(xf)'|+f\). For \(d=1+j-2\Theta,\ m=U+dv^2/2>0,\ B_0=e^{dU+d^2v^2/4}\), the full integral over \(x\ge1\) is bounded by \(B_0[v\sqrt\pi m+v^2e^{-m^2/v^2}/2]\) and \(\max xf\le B_0(m+v)\). Both follow by shifting the Gaussian in \(u=\log x\).

## Retaining the signed off-diagonal terms

Fix an arbitrary submultiset \(\mathcal S\) of \(R\) of the right zeros, a cutoff \(\eta<s\), and a distance \(D>0\). Use \(J=[H-10,T+10]\). For \(1<c<2\) and \(\gamma_i\in[H,T]\) the positive sum
\[
 \mathfrak P_c(x)=\sum_\rho\frac{c-\beta}{(c-\beta)^2+(x-\gamma)^2}
 \le P_c=\tfrac12\log[(T+3)/(2\pi)]-\zeta'(c)/\zeta(c)+10^{-8}
\]
holds at \(x=\gamma_i\) by the logarithmic derivative of \(\xi\), the absolutely convergent Euler series and the digamma bound from the earlier certificate. For \(c=2\) and arbitrary real \(t\), the same formula and \(|\psi(1+it/2)-\log(1+it/2)|\le1\) give \(\mathfrak P_2(t)\le\tfrac12\log(|t|+2)+3\). [Poisson-kernel certificate](../../round7/qrh_strip/RIGHT_EDGE.md)

For one reflected pair \(\beta,1-\beta\) at \(\gamma\) with \(\beta\ge1/2\), set \(h=c-1/2,\ z=(\beta-1/2)^2,\ y=(\gamma_i-\gamma)^2\). The ratio of the Gaussian ordinate weight to the sum of the two Poisson weights is
\[
 A_z(y)=\frac{e^{-v^2y/4}}{2h}\left[h^2-z+y+\frac{4zy}{h^2-z+y}\right].       \tag{3}
\]
The bracket is convex in \(z\) and concave in \(y\). To bound it times the exponential over a rectangle \(z_1\le z\le z_2,\ y\ge y_0\), take both \(z\)-endpoints, bound each bracket by its tangent at \(y_0\), then maximize that affine function times the exponential exactly. This is paired_ratio. The sum \(k(\Theta-\beta)+k(\Theta+\beta-1)\) is nondecreasing in \(\beta\ge1/2\) by convexity of \(k\); \(k\) is decreasing on \([0,.75]\) in all rows.

The following is a uniform charge per \(k(a_i)\) for all omitted terms of (1). Split \([1/2,\eta]\) evenly into 16 intervals. In each take the upper endpoint of the preceding \(k\)-sum and the (3) bound on \(y\ge0\). For \(\eta\le\beta\le\Theta,\ y\ge D^2\), take \([1+k(2\Theta-1)]\) times the (3) bound there. For omitted left members of near pairs with \(\beta>\eta\), take \(k(\Theta+\eta-1)\) times the (3) bound on \(y\ge0\). The maximum of these charges is a bound against a *single* total Poisson mass. Remove the actual pair at \(\gamma_i\), paying its left member separately by \(k(\Theta+s-1)\). The remaining mass is at most \(P_c-2h/[h^2-(s-1/2)^2]\). Critical-line roots can be represented by half of a coincident reflected pair, preserving exactly the available mass. Coincident right-hand zeros have positive inner product and can be dropped from a lower bound. Call the resulting absolute charge \(A_0\).

On the whole real line \(\sum |g_i(t)|\le(1+\Theta)\mathfrak P_2(t)\), since \(k\le1\), \(2-\beta\le1+\Theta\), and \(v^2/2\ge(2-\Theta)^{-2}\). Thus completing each mixed integral \(\langle \sum_\rho g_\rho,g_i\rangle_J\) to the real line costs at most \(k(a_i)e_b\), where
\[
 e_b=2(1+\Theta)\frac{e^{-v^2b^2/2}}{v^2}
       \left[\frac{\tfrac12\log(T+2)+3}{b}+1\right],\qquad b=10.
\]
This follows by integrating the Gaussian tails in \(u=|t-\gamma_i|\ge b\) using \(\log(|t|+2)\le\log(T+2)+u\). These bounds justify absolute interchanges of the zero sum with each scalar product. The term with \(-\|\sum_{i\in\mathcal S}g_i\|_J^2\) may be bounded below by its negative full-line value.

For \(0<\lambda\le1\) put \(q_\lambda=2/(2-\lambda)\), \(m=k(\Theta-s)\), \(C=A_0+\sqrt2\|E\|_\infty+e_b/d_0\), using (2) on the right. Expanding \(\|P-\lambda\sum_{i\in\mathcal S}g_i\|_J^2\ge0\) as a lower bound on \(\|P\|_J^2\), dividing by \(\lambda(2-\lambda)d_0\), and retaining signed neighbors gives
\[
 -\sum_{i\in\mathcal S}\sum_{\substack{\beta_j>\eta\\0<|\gamma_i-\gamma_j|\le D}}
       c_{ij}\Omega_{ij}\ \ge\ R p-E_0,\quad
 p=m^2-q_\lambda m C,\qquad
 E_0=\frac{(|J|+4.2)S_0+4.2S_1}{M^2d_0\lambda(2-\lambda)}.              \tag{4}
\]
Here \(c_{ij}=1\) for \(j\in\mathcal S\), otherwise \(q_\lambda\). The price for (2) follows from \(\int |g_i|/d_0=\sqrt2 k(a_i)\). The remaining terms have absolute coefficients bounded by \(q_\lambda\). In all rows \((2-\lambda)m>C\), so \(k_i^2-q_\lambda k_i C\) is nondecreasing for \(k_i\ge m\). This proves (4) for *every* submultiset, including submultisets selected after inspecting their neighbors.

Choosing the submultiset of roots without a negative neighbor forces \(R\le\lfloor E_0/p\rfloor\). If the whole rectangle contains at least 420071 roots, its signed deficit on the left of (4), divided by \(R\), exceeds the last column.

| \(\eta\) | \(D\) | \(U\) | \(v\) | \(c\) | \(\lambda\) | cap without a negative neighbor | signed deficit per root, lower bound |
|---:|---:|---:|---:|---:|---:|---:|---:|
| .70 | 2 | 30.53 | 2.83 | 1.39 | .88 | 144451 | .32930 |
| .75 | 2 | 30.69 | 2.42 | 1.33 | .70 | 178614 | .22823 |
| .77 | 1.5 | 31.15 | 2.98 | 1.26 | .70 | 267150 | .11332 |
| .78 | 1.5 | 31.22 | 2.94 | 1.27 | .60 | 352421 | .04100 |
| .784 | 1.5 | 31.30 | 3.01 | 1.27 | .59 | 410976 | .00488 |
| .75 | 1.1 | 31.50 | 3.90 | 1.27 | .64 | 357603 | .04878 |

## A separate pointwise isolation bound

A right root is ordinarily isolated at \((\eta,D)\) if no other right zero with \(\beta'>\eta\) lies within distance \(D\), counting a second occurrence of a multiple root. The intervals \([\gamma_i-r,\gamma_i+r]\) about these roots have disjoint interiors when \(2r\le D\). At \(t=\gamma_i+y,\ |y|\le r\), the own reflected pair gives at least \([k(\Theta-s)-k(\Theta+s-1)]e^{-v^2y^2/2}\) in modulus. Each low pair contributes at most its Poisson mass times
\[
 \tfrac h2 [k(\Theta-\eta)+k(\Theta+\eta-1)]
       \sup_{u\ge0}(1+u^2/(c-\eta)^2)e^{-v^2u^2/2}.
\]
Indeed the pair Poisson mass is at least \((2/h)/(1+u^2/(c-\eta)^2)\) by adding the two center weights with their individual denominator perturbations. For high pairs use \(c-\Theta,\ u\ge D-|y|\), and \(1+k(2\Theta-1)\) in the same formula. The own Poisson mass is at least \((2/h)/(1+y^2/(c-\Theta)^2)\). Take the greater of the two charges against \(P_c\) minus this own mass, evaluating \(P_c\) with height endpoint \(T+r\). Subtract this and an allowance for (2), take the positive part, and square. The resulting lower bound decreases on \(0\le y\le r\) and is integrated with 1024 lower rectangles. The even prime allowance here splits the sum at \(\log n=U/2\), using respectively Gaussian decay and geometric decay. Summing over disjoint intervals and dividing the arithmetic energy by this one-root cost proves the following caps.

| \(\eta\) | \(D\) | \(U,v,r,c\) | cap for ordinary isolated roots |
|---:|---:|---|---:|
| .70 | 3 | 30.2, 1.9, 1, 1.38 | 120909 |
| .75 | 2 | 30.9, 2.65, .69, 1.26 | 219844 |
| .76 | 2 | 31, 2.66, .63, 1.26 | 273003 |
| .77 | 3 | 31.3, 2.44, .65, 1.30 | 369455 |

The optional phase version in the pointwise script counts a root if every other high right neighbor within \(D\) has nonnegative scalar product of its packet with the selected root's packet at each time within \(r\) of the latter's ordinate. At a given time collect all active selected roots and all near high right terms having nonnegative scalar products with every active selected term. Those terms contain all active selected roots: their mutual ordinate distances are at most \(2r\), and a repeated ordinate satisfies the phase test when \(v^2(\Theta-\eta)r<\pi/2\). Relative to each active selected root, any excluded high right term must be at least \(D-r\) from this time (a deficient scalar product against some active selected root suffices). The collected sum has norm at least the square root of the sum of the selected squared norms, by projecting on the sum of active selected packets. The triangle bound and \((\sqrt{\sum x_i^2}-b)_+^2\ge\sum(x_i-b)_+^2\) then allow the same positive error to be charged per active root. The code keeps the left partners and pays the self mirror separately with its own Gaussian decay. The signed theorem (4) does not require this option.

Reproduce the independent Arb bounds in this directory with:

~~~powershell
python -B paired_packet.py
python -B isolated_packet.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
