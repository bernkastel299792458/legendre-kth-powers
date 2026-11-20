# A finite thin-band target and certified signed adjacent products

Take \(T=H=3\cdot10^{12}, D=T/10,\ \sigma=7/8,\ X=10^{10}\) in the [weight replacement theorem](README.md). In its elementary sum (1), retain only
\[
 t\in[T,4T],\qquad
 0<D|\log(k/l)|\le18,\qquad
 mn=\frac{kl}{de}\le N_*=\frac{4T}{2\pi}e^{20}.
 \tag{1}
\]
Call the resulting scaled Gaussian integral \(S_*\). Then
\[
 \left|X^{3/4}\int_I W_T(t)\mathcal O_X(t)\,dt-S_*\right|
       < 0.00001390 .
\]
This includes the actual direct and reflected Gamma weights. If the existing sharp-mollifier arithmetic table from the common-window note is accepted, \(S_*\le0.20998\) suffices for the sample's \(B=1\) variance bound after dropping its nonpositive complete reflected residue. Thus estimating a single explicit finite signed expression suffices for this sample of the variance problem. Even at this sample, the product bound allows \(k,l\) up to \(X\sqrt{N_*}\exp(9/D)>10^{20}\), and the inequality for \(S_*\) remains open. [Arb checks](check_gamma.py) · [Variance implication and arithmetic-table input](../../round2/afe/GAUSSIAN_WINDOW.md)

## Absolute cost outside (1)

For complex height \(z\) with \(\Re z\ge H\), use the principal logarithm for \(s=\log(2\pi mn/z)\). Integrating the elementary Gaussian horizontally gives
\[
 |\Phi(x+iy)|\le e^{y^2/4}\Phi(x),\qquad
 |F_r(x+iy)|\le e^{y^2/4}(1+e^{rx})\Phi(x).
\]
Thus \(|y|\le\pi/2\). Put \(U_T=T/(2\pi)\) and define
\[
 B_0=\frac{2eX U_T^{1-\sigma}(1+\log U_T)^2}{(1-\sigma)^2},
 \qquad B_1=e^{4+\pi^2/16}B_0.
\]
Before multiplication by \(W_T\) and by the oscillation, the absolute sum of all scaled complex terms is bounded by \(B_1\max(1,|z|/T)\). Indeed use \(\Phi(\log v)\le e^4\min(1,v^{-2})\) and the two divisor-sum bounds in the weight theorem. For \(|z|\ge T\), the change from \(T\) to \(|z|\) costs at most \((|z|/T)^{1-\sigma+2/(1+\log U_T)}\le |z|/T\). The same bound applies at negative real heights by symmetry of the weights.

Write the cosine as the real part of \(e^{it\lambda}\) with \(\lambda=\log(k/l)\). Shift each positive integration ray \([T,\infty)\) vertically by \(5iD\,\mathrm{sgn}(\lambda)\). On the horizontal ray with \(D|\lambda|>18\), the exponential factor relative to the real Gaussian is at most \(e^{25-90}\). The normalized Gaussian integral of \(\max(1,|z|/T)\) is at most 4, from \(|z|/T\le2.5+|t-2T|/T\). On the vertical joining segment, \(\max(1,|z|/T)<1.5\), while the Gaussian costs at most \(e^{-75}/(\sqrt\pi D)\). Its length is \(5D\). On the negative ray \(t\le-T\), put \(w=(2T-t)/D\ge30\). Integrating \((3+w/10)e^{-w^2}/\sqrt\pi\) gives less than \(e^{-400}\). All contour manipulations can first be made termwise on a finite sum. The absolute bounds on each line and segment allow passage to the complete sum; splitting \(\lambda>0\) and \(\lambda<0\) costs no extra factor because the coefficient majorants are identical on the two lines and bound arbitrary subsets by addition. Thus dropping all large frequencies costs less than
\[
 B_1(4e^{-65}+8e^{-75}+e^{-400})<1.864\cdot10^{-9}.
\]

To truncate the remaining real heights to \([T,4T]\), the two tails have standardized distances at least 20 and 30 from the Gaussian center, yielding total cost below \(B_1 e^{-395}\) from the preceding linear height envelope. On the retained heights, \(mn>N_*\) implies \(v=mn/U>e^{20}\). Gaussian exponential moments give \(\Phi(\log v)\le e^{100}v^{-10}\le e^{-60}v^{-2}\). Hence omitting these products costs at most \(4B_0 e^{-60}<2.734\cdot10^{-9}\), allowing \(|t|/T\le4\). Adding the full Gamma replacement cost proves the claim.

## Signed blocks at the target height scale

For each row below take integer \(k=A,\ldots,A+15,\ l=k+h\), \(h=1,2,3,4\), and include both orderings. All squarefree divisors \(d\mid k,\ e\mid l\) up to \(X\) are included with their actual signs. All heights in \(I\) and both actual AFE branches are included. The second column measures their scaled signed contribution. The final column divides it by a positive upper bound obtained from the elementary kernel \(F_r\) by replacing each Möbius product with its absolute value, removing the cosine, and adding the per-term Gamma error \(3200/H^2\) specified below.

| \(A-T\) | Scaled signed contribution | Signed / positive comparison |
|---:|---:|---:|
| \(0\) | \((-8.617,-8.615)\cdot10^{-15}\) | \((-0.000836,-0.000834)\) |
| \(1\,414\,213\) | \((-4.882,-4.880)\cdot10^{-14}\) | \((-0.002807,-0.002805)\) |
| \(2\,718\,281\) | \((9.426,9.429)\cdot10^{-15}\) | \((0.000667,0.000669)\) |
| \(3\,141\,592\) | \((-2.816,-2.813)\cdot10^{-15}\) | \((-0.000112,-0.000110)\) |

For example the \(h=1\) terms alone are negative at the first row and positive at the fourth row. These are certified finite contributions, including one positive combined block. Their signs and small ratios give no uniform upper estimate on other blocks.

In the [block verifier](check_block.py), factor each integer \(k,l\) exactly with FLINT and form the products of all distinct subsets of its prime divisors up to \(X\). For each pair combine terms with identical \(mn\) using exact signed integer coefficients. The height integral after Gamma replacement is evaluated on \(-8\le w=(t-2T)/D\le8\), on 16 unit panels, each with the 12-point Gauss–Legendre formula. For a unit panel center \(w_0\), the exact integrand per coefficient, including the Gaussian and the cosine, is holomorphic on \(|w-w_0|\le2\) and has modulus \(<1000\). In fact \(|\arg(1+w/20)|<0.2\), \(D|\log(k/l)|\le0.8\), \(|e^{-w^2}|\le e^4\), and \((1+e^{rx})\Phi(x)\le1+e^{r^2}<2.76\) by the Gaussian moment. The same bound holds after removing the cosine. Cauchy's coefficient bound implies a Taylor remainder at degree 23 on that panel of size \(\le1000(1/4)^{24}/(1-1/4)\). Since Gauss–Legendre weights are positive, have mass one per panel, and integrate through degree 23 exactly, the summed all-panel error is at most 32 times this remainder. For \(|w|>8\), the real integrand before the Gaussian is at most 3, so omitting the rest of \(I\) costs \(\le3\operatorname{erfc}(8)\) per coefficient. The pointwise actual Gamma replacement costs at most \(3200/H^2\) after extraction of \((kl)^{-\sigma}\), since both \(\min(1,v^{-2})\) and \(v^r\min(1,v^{-2})\) are at most 1. The program adds these three errors to both sides of every reported interval, which encloses the signed Gamma sum and the positive comparison just described.

To reproduce a row, run the following in this directory and change the starting integer as indicated in the table.

~~~text
python -B check_block.py --start 3000000000000 --length 16 --shifts 4
~~~

2026-11-20. Claude and Codex project attribution. Codex derived the frequency and product estimates and ran the signed-block checks.
