# Cancellation of the continuous shifted convolution term

Set \(H=3\cdot10^{12}\), \(0.70\le\sigma\le7/8\), \(r=2\sigma-1\), \(t\ge H\), \(U=t/(2\pi)\), \(1\le X\le10^{14}\). Use the sharp mollifier and the two actual Gamma weights of the [square AFE](../../round2/afe/README.md). Write \(\mathcal D,\mathcal O\) for its diagonal and non-diagonal terms. For every primitive ratio of mollifier indices and each nonzero integer shift, replace its arithmetic progression sum by the integral with the same density. Denote the sum of those integrals, specified in (2), by \(\mathcal C\). Then
\[
 |\mathcal D(t)+\mathcal C(t)-R_1-R_2(t)|
       \le e^{-t/3} U^{-r-7/20}.                                      \tag{1}
\]
Here \(R_1=1+Q_X\) and \(R_2(t)\le0\) are the two residues in the square AFE. This holds pointwise, before averaging in height. It applies to all shifts, all \(d,e\le X\), and the exact two Gamma branches. The remaining non-diagonal problem is the difference between an arithmetic progression sum and its integral rather than the size of the integral. A quantitative sufficient inequality for the actual progression discrepancy appears below.

## Defining the arithmetic progression and its integral

For mollifier indices \(d,e\), write \(g=(d,e),d=ga,e=gb,\ (a,b)=1,\ p=ab\). For \(h=am-bn>0\), put \(v=bn\). Exactly the positive integers \(v\equiv0\bmod b,\ v\equiv-h\bmod a\) occur. This is a single residue class modulo \(p\), including \(v\equiv0\bmod p\) when appropriate. Write
\[
 L_t(y)=V_{\sigma,t}(y)+q_t y^rV_{1-\sigma,t}(y),\qquad
 f_{p,h,t}(v)=[v(v+h)]^{-\sigma}
 L_t\left(\frac{v(v+h)}p\right)
 \left[\left(\frac{v+h}{v}\right)^{it}+
       \left(\frac{v+h}{v}\right)^{-it}\right].
\]
The sum over the two directions uses interchange of \(d,e\) and \(m,n\) in one direction. This is allowed since we sum the whole ordered set. With \(c_{gab}=\mu(ga)\mu(gb)g^{-2\sigma}\), the respective quantities are
\[
 \mathcal O=\sum_{g,a,b}c_{gab}\sum_{h\ge1}
      \sum_{\substack{v>0\\ v\equiv0\bmod b\\v\equiv-h\bmod a}} f_{p,h,t}(v),
 \qquad
 \mathcal C=\sum_{g,a,b}c_{gab}\sum_{h\ge1}\frac1p
          \int_0^\infty f_{p,h,t}(v)\,dv .                           \tag{2}
\]
All \(g,a,b\) sums are finite with \(ga,gb\le X\). Each continuum integral exists as an ordinary absolutely convergent integral for fixed \(h\). Its value, after the height phase is included, is \(O_t(h^{-r-7/10})\), as shown below. Thus the outer sum of these values converges absolutely; an absolute value inside every integral before summing \(h\) would be a different quantity.

## The beta integral and matching arithmetic weights

Let \(h_t(w)=\Gamma_{\mathbb R}(w+it)\Gamma_{\mathbb R}(w-it)\) and let \(G_t(z)\) be the even Gaussian times the four pole-removing factors in the square AFE. Define
\[
 P_t(z)=\frac{G_t(z)}z+\frac{G_t(z+r)}{z+r},\quad
 A_X(z)=\sum_{g,a,b}\frac{\mu(ga)\mu(gb)}{g^{2\sigma}}(ab)^{z-1}
 =\sum_{d,e\le X}\mu(d)\mu(e)\frac{(d,e)^{1-r-2z}}{(de)^{1-z}} .
\]
This is \(D_X(-z)\) of the square AFE. Directly on any line \(0<c<1-\sigma\),
\[
 L_t(y)=\frac1{2\pi i}\int_{(c)}
          \frac{h_t(\sigma+z)}{h_t(\sigma)}P_t(z)y^{-z}\,dz .
\]
For the second term of \(L_t\), change the original Mellin variable to \(z+r\), and shift both lines to \(c\); only positive real parts occur. This formula bounds the weight by \(O_t(y^{-c})\), which ensures convergence of each integral at zero as well as infinity since \(1/2<\sigma+c<1\).

Put \(w=\sigma+z,\ s=2w-1=r+2z\). For each of the two phases use \(v/(v+h)\) in the real integral. The result is \(h^{-s}B(1-w\mp it,s)\). The restrictions \(0<\Re(1-w),0<\Re s\) allow ordinary absolute interchange of the \(v,z\) integrals on the initial line. [Euler beta integral](https://dlmf.nist.gov/5.12#E1)

For **each fixed \(h\)** now shift the Mellin line to \(\Re z=\delta=7/20\). The only possible beta poles \(z=1-\sigma\pm it\) are removable after multiplication by \(P_t(z)\). Indeed the two \(G_t\) arguments are \(1-\sigma\pm it\) and \(\sigma\pm it\), respectively, and both are zeros of the polynomial. The factor \(\Gamma(s)\) stays regular throughout. On horizontal edges with \(|\Im z|\to\infty\), ordinary Stirling bounds give at most exponential-linear growth in \(|\Im z|\) before the Gaussian factor, uniformly in the compact range of real parts at fixed \(t\). The same absolute convergence on the shifted line provides the stated bound for the \(h\)-integral. Since \(\Re s=r+2\delta\ge1.1\), the series of these shifted integrals is absolutely summable; summing produces \(\zeta(s)\). It follows that \(\mathcal C\) is the \(1/(2\pi i)\) integral on \((\delta)\) of
\[
 \frac{P_t(z)A_X(z)}{h_t(\sigma)}
 h_t(w)\zeta(s)[B(1-w-it,s)+B(1-w+it,s)] .
\]

## Exact archimedean identity

Write \(s_1=w+it,s_2=w-it\). Duplication and reflection of Gamma yield
\[
 \frac{h_t(w)}{h_t(1-w)}\frac{\Gamma(1-s_1)}{\Gamma(s_2)}
 =(2\pi)^{-s}\frac{\cos(\pi s_2/2)}{\sin(\pi s_1/2)}.
\]
Add the identity with \(s_1,s_2\) interchanged. The sum of the two trigonometric quotients is
\[
 2\sin(\pi w)\,
 \frac{\cosh(\pi t)}{\cosh(\pi t)-\cos(\pi w)} .
\]
Since \(\sin(\pi w)=\cos(\pi s/2)\), the zeta functional equation gives the exact formula
\[
 h_t(w)\zeta(s)\,[B(1-w-it,s)+B(1-w+it,s)]
 =h_t(1-w)\zeta(1-s)J_t(w),\qquad
 J_t(w)=\frac{\cosh(\pi t)}{\cosh(\pi t)-\cos(\pi w)} .              \tag{3}
\]
These are identities of meromorphic functions away from the indicated poles. [Gamma reflection and duplication](https://dlmf.nist.gov/5.5) · [Zeta functional equation](https://dlmf.nist.gov/25.4#E1)

The earlier exact diagonal remainder \(\mathcal E=\mathcal D-R_1-R_2\) becomes the negative integral of
\[
 B_t(z)=\frac{h_t(1-\sigma-z)}{h_t(\sigma)}
              \zeta(1-r-2z) A_X(z) P_t(z)
\]
on \((\delta)\), with the factor \(1/(2\pi i)\). Substitute \(v=-z\) into the common contour in the square AFE; the upward orientation returns, while evenness of \(G_t\) contributes the minus sign from the two denominators. Thus \(\mathcal D+\mathcal C-R_1-R_2\) is the integral of \(B_t(z)(J_t(w)-1)\) on this very line.

Because \(1.05\le\Re w\le1.225\), \(\Re\cos(\pi w)<0\). Hence \(|J_t(w)-1|\le1\), from \(|A-c|^2\ge|c|^2\) for positive real \(A=\cosh(\pi t)\) and \(\Re c<0\). If \(|\Im z|\le t/2\), the same quotient is at most \(2e^{-\pi t/2}\) since \(|\cos(\pi w)|\le\cosh(\pi\Im z)\). The square AFE's §§3–4 bound the normalized integral of \(|B_t|\) itself, including the central region, by \(6490U^{-r-\delta}\). On each outer ray \(|\Im z|>t/2\), its normalized integrand before \(1/(2\pi)\) is at most \(e^{-|\Im z|}\), by the explicit large-ordinate bound there. Combining gives \((12980e^{-\pi t/2}+e^{-t/2})U^{-r-\delta}\le e^{-t/3}U^{-r-\delta}\). This proves (1).

## Remaining estimate in the Gaussian window

Let \(\mathcal L(t)=\mathcal O(t)-\mathcal C(t)\). With \(W_T,I\) as in the [common-window calculation](../../round2/afe/GAUSSIAN_WINDOW.md), its first-moment cost is less than \(1.81\cdot10^{-8}\) and its low-band cost less than \(3\cdot10^{-12}\), after scaling by \(X^r\). In the entire previous range \(T\ge H,\ X\le\min(T^{7/8},10^{14})\), the exponential term of (1) after scaling is at most \((10^{14})^{3/4}e^{-H/3}<10^{-20}\). Therefore the following is sufficient for the normalized variance bound \(B\):
\[
 X^r\left[Q_X+\int_I W_T(t)
              \big(\mathcal L(t)+R_2(t)\big)\,dt\right]
 \le B-0.000000019.                                                  \tag{4}
\]
The \(0.078545\) and \(0.263337\) reservations of the earlier implication have been superseded **for this modified remaining term \(\mathcal L\)**. At \(T=H,\ \sigma=7/8,\ X=10^{10}\), the existing sharp table gives \(X^rQ_X<0.533564/r\). Taking this upstream arithmetic input, an upper bound of \(0.28858\) on the scaled integral of \(\mathcal L\) suffices for \(B=1\), even if the nonpositive \(R_2\) is discarded. The actual required bound on \(\mathcal L\), or an equivalent signed lattice sum, remains open.

There is an exact version with a single discontinuous periodic function per progression. Let \(b_1(u)=\{u\}-1/2\), choose the representative \(v_0\) of the progression in (2), and set \(a_0=1/2\). Its contribution to \(\mathcal L\), before multiplication by \(c_{gab}\), is
\[
 -p^{-1}\int_0^{a_0} f(v)\,dv
 + b_1((a_0-v_0)/p) f(a_0)
 + \int_{a_0}^\infty b_1((v-v_0)/p) f'(v)\,dv .                    \tag{5}
\]
This follows from the distributional derivative of the periodic sawtooth and an integration by parts; there is no lattice point in \((0,a_0]\). At large \(v\), the Mellin definition gives arbitrary polynomial decay also after differentiating. The terms in (5) are grouped for each \(h\) before the convergent summation in (2). Formula (5) isolates the modular inverse in \(v_0\) and gives a precise signed discrepancy target.

2026-11-20. Claude and Codex project attribution. Codex derived the actual-weight identity and quantitative comparison.
