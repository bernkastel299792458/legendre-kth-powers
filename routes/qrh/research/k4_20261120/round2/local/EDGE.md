# Crossing the verified height in the finite-height signed test

For each row, every real \(x\) with \(L=\log x\) in the stated range has a prime in the open interval \((x,x+4x^{3/4})\).

| Inputs | Range of \(L\) | Largest integer \(n\) at \(x=n^4\) |
|---|---|---:|
| Published finite RH and classical Brun–Titchmarsh | \([114.992,115.00099]\) | 3,062,484,100,155 |
| Same with QRH(7/8) | \([114.992,115.0009967]\) | 3,062,489,229,820 |
| Finite RH and Yamada's preprint Theorem 2 | \([115.017,115.02548]\) | 3,081,291,674,997 |
| Same with QRH(7/8) | \([115.017,115.0254897]\) | 3,081,299,147,138 |

The earlier [lower endpoints](../low_sieve/PROOF.md) supply the connections on the left. The proof uses the signed test and explicit formula of the [finite-height argument](../../lower/PROOF.md). All four rows use the exact verified height \(H=3\,000\,175\,332\,800\) of [Platt and Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765). The numerical assertions, including the integer endpoints, use Arb. [Scalar certificate](check_edge.py)

## Arithmetic bounds

Maintain the former notation \(d(L)=\tfrac12\log(1+4e^{-L/4})\), \(c=L+d\), \(I=\pi\sin(a)/a\), and set \(Q=10^4\). For a row with endpoints \(l,h\) use \(a=(1-10^{-12})K d(h)\), so that \(Kd(L)>a\) throughout. Use \(r=10^{-6}\) for the near-center prime estimate and \(R=0.01\) for the elementary Gaussian tail. The earlier pole, archimedean and verified-zero estimates use the new constants. Its estimates (4) and (5) use \(R\) in place of the former radius. The Gaussian has \(QR=100\).

For a layer of angular length \(w\) in the \(u=K(\log p-c)\) coordinate and one connected component, apply the Brun–Titchmarsh tangent to \(2y/(\log y+\eta)\) at \(s e^c/K\), with \(\eta=0\) or \(0.8601\). Inside \(|\log p-c|\le t\), the normalized cost per unit level is bounded by \(C_1(s,t)w+C_2(s,t)\), where

\[
 v=l-\log K+\eta+\log s,\quad m=\frac{2(l+t)e^{t/2}}{Iv^2},\qquad
 C_1=m e^t(v-1),\quad C_2=ms.
\]

The formulas with \(c\) in place of \(l\) bound the cost by applying the tangent, the log-coordinate Jacobian and the prime weight. Both coefficients decrease for \(c\ge l\), as in the earlier proof with \(J=\log K-\eta-\log s+t>2\) and \(v>4\). The program checks these inequalities and that each tangent intercept exceeds 10. The tangent then covers lengths below \(e^2\) by integer counting. [Montgomery and Vaughan, Theorem 2](https://doi.org/10.1112/S0025579300004708) · [Yamada, v1, Theorem 2](https://arxiv.org/pdf/2312.16090v1)

In the region \(|u|\le Kr\) extend the upper bounds on lengths and peaks to the whole positive exterior lobes. Each truncated length and peak is at most the original one. Use scale \(s=1.55\) on all secondary lobes. Bound their summed peaks for indices \(j=1,\ldots,64\) and both signs by dividing each angular lobe into 32 equal pieces. On a piece \([u_0,u_1]\), use for the positive numerator the smaller of \(1+\cos a\) and \(\cos a-\cos((u_0+u_1)/2)+(u_1-u_0)/2\). Use \(u_0^2-a^2\) for the denominator. For \(j>64\), comparison with \(\sum_{j>64}j^{-2}\le1/64\) suffices.

On the first positive exterior lobe \(a\le u\le2\pi-a\), \(g\) decreases from \(\sin(a)/(2a)\) to zero. Divide its angular width into 256 equal parts. For consecutive widths \(w_0,w_1\) from the left endpoint, the heights between \(g(a+w_1)\) and \(g(a+w_0)\) have total size \(\delta>0\), and their individual superlevel lengths lie in \([w_0,w_1]\). Apply their tangent at \(s'=(w_0+w_1)/2\). To preserve the exact total positive exterior area, first charge all lengths at slope \(C_1(s,r)\) using \(\int_{|u|>a}g_+(u)\,du=(1-a/\pi)I\). The two first lobes then require the adjustment

\[
 2\delta\left[C_2(s',r)+
 \max_{w\in\{w_0,w_1\}}\{(C_1(s',r)-C_1(s,r))w\}\right]
\]

for each pair of corresponding height bands. This handles either sign of the slope difference. The base intercept is charged only for the secondary lobes.

For \(Kr<|u|\le KR\), overcount the exterior again with coefficients \(C_1(1,R),C_2(1,R)\). The total angular area is at most \(4/((Kr)(1-(a/(Kr))^2))\), from the rational bound for \(g\). All possible lobes have \(j\ge j_0=\lfloor Kr/(2\pi)\rfloor-1>1\). Their summed peaks are at most \((1+\cos a)/(2\pi^2(j_0-1))\), again by summing \(j^{-2}\).

## A local count above the true RH cutoff

In the two QRH rows take \(K=H+S,\ S=300\,000\). The unsmoothed spectrum is zero for \(|t|>K\) and satisfies \(0\le G_0(t)\le\pi(K-t)_+/K^2\) for all real \(t\). This follows from \(\sin u\le u\) for \(u\ge0\) and \(K-|t|\le K-t\). Write \(X\) for a centered Gaussian of variance \(2Q^2\). Taking absolute values in the entire Gaussian convolution gives

\[
 |G(\gamma-i(\beta-\tfrac12))|
 \le \frac{\pi e^{1/(16Q^2)}}{K^2}\,
       \mathbb E(K+X-\gamma)_+ .
\]

For \(v\ge0\) put \(N_H(v)=N(H+v)-N(H)\), counting positive ordinates with multiplicity and including the upper endpoint. The error estimate of [Carneiro, Milinovich and Soundararajan, Lemma 9](https://arxiv.org/pdf/1708.04122) and \(\log(1+v/H)\le v/H\) yield

\[
 N_H(v)\le C+Mv+\frac{v^2}{4\pi H},\quad
 C=0.3\log H+6,\qquad M=\frac{\log(H/(2\pi))}{2\pi}+\frac{0.15}{H}.
\]

The derivative of the counting main term at \(H+v\) is \(\log((H+v)/(2\pi))/(2\pi)\). Subtracting at the fixed lower endpoint cancels its entire main term. For \(Y=(S+X)_+\) the triangular sum averaged over the Gaussian is exactly \(\mathbb E\int_0^Y N_H(v)\,dv\), by nonnegative interchange. Therefore the normalized contribution of all unverified zeros is at most

\[
 E=\frac{\pi e^{1/(16Q^2)}}{IK}(e^{-l/8}+e^{-7l/8})
 \left(C\,\mathbb EY+\tfrac12 M\,\mathbb EY^2+
             \frac{\mathbb EY^3}{12\pi H}\right).
\]

Here \(2\cosh(3c/8)e^{-c/2}=e^{-c/8}+e^{-7c/8}\) accounts for positive and negative ordinates under QRH and zero symmetry. For \(S\ge0\), use \(\mathbb EY\le S+Q/\sqrt\pi\), \(\mathbb EY^2\le S^2+2Q^2\), and \(\mathbb EY^3\le \mathbb E(S+|X|)^3\). The required absolute moments of \(X\) of orders \(1,2,3\) are \(2Q/\sqrt\pi,2Q^2,8Q^3/\sqrt\pi\). In the two finite-RH rows use \(S=-128Q\) and the previous Gaussian-tail argument independent of QRH.

At the QRH endpoints the full normalized costs are below \(0.999999966\) and \(0.999999959\), respectively. At \(K=H\), the same certificate using the same endpoint function \(a=(1-10^{-12})K d(h)\) returns costs above \(1.000000050\) and \(1.000000042\). With \(S\) larger than the Gaussian width, the leading term in \(E\) is quadratic in \(S\), whereas the exterior length benefit to first order is linear. These comparisons refer to this numerical upper-bound formula.

## Broadening the kernel at \(L=116,120\)

The [symmetric spectral model](SINGLE_GAP.md) satisfies the finite-RH location, QRH, total counts, CS density inequalities and the positive K5 global budget used for the block argument. Set \(n=\lceil e^{L/4}\rceil\), \(D_0=2\log(1+1/n)\), \(c_0=4\log n+D_0\). The model is built for this \(c_0\). For any \(1.85\le a\le2.5\), \(K\ge H\) such that \(a/K\le D_0\), the model already forces the normalized absolute zero cost for the signed kernel to exceed **1.63 at \(L=116\)** and **2.98 at \(L=120\)**. Here \(Q=10^4\) and the normalization is \(e^{c_0/2}I/K\).

Indeed \(G_0\) is globally Lipschitz with constant \(\pi/K^2\), including the support boundaries. For every \(|b'|\le1/2\), Gaussian convolution and \(|e^{iu}-1|\le|u|\) give
\[
 |G(\gamma-i b')-G_0(\gamma)|\le\frac{\pi}{aK}\epsilon,\qquad
 \epsilon=\frac{2(2.5)Q}{H\sqrt\pi}+e^{1/(16Q^2)}-1
                +\frac{e^{1/(16Q^2)}}{2Q\sqrt\pi}.
\]
The first term bounds the effect of real Gaussian smoothing using \(\mathbb E|X|=2Q/\sqrt\pi\). The last two bound the complex Gaussian multiplier minus 1.

Each model point in \(H<\gamma<H+W\), \(W=10^8\), has \(v=a\gamma/K\le w=(H+W)D_0<1.85\). Thus \(\gamma<K\), and the unsmoothed spectral ratio is \(\sin(a-v)/\sin a\). By concavity of sine on \([a-w,a]\), this ratio is at least \(\min(1,\sin(a-w)/\sin a)\). The second expression is increasing in \(a\), since it equals \(\cos w-\cot(a)\sin w\). Also \(\sin a\ge\sin(2.5)\). For each of the \(m=5\cdot10^6\) symmetric quartets at \(b=0.8748\), the real part of the cosine test is positive at the resonant center because \(e^{i\gamma c_0}=1\). Summing those four real parts and using \(4\cosh((b-1/2)c_0)e^{-c_0/2}\ge2e^{(b-1)c_0}\) gives a lower bound on the total absolute cost:
\[
 2m e^{(b-1)c_0}
 \left(\min\left(1,\frac{\sin(1.85-w)}{\sin(1.85)}\right)
                         -\frac{\epsilon}{\sin(2.5)}\right).
\]
It exceeds the stated values by the [Arb computation](check_single.py). Thus transferring the K5 aggregate budget and the CS counts alone into an absolute spectral bound for this range of signed tests cannot supply pointwise coverage at the two indicated fourth-power intervals. This conclusion concerns the synthetic spectrum and these particular aggregate inputs.
