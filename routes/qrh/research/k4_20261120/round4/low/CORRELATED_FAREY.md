# The joint Farey-neighbor distribution extends the proved lower range

For every real \(x\) with \(115.032114\le\log x\le115.033338\), there is a prime in \((x,x+4x^{3/4})\), using the published finite-height and sieve inputs. Adding QRH(7/8) extends the upper endpoint to **\(115.033340\)**. Joined to the [previous lower range](../../round3/low/FAREY.md) this covers all integers \(n\le3\,087\,352\,365\,817\) in the fourth-power problem. The new sieve inequality is
\[
 \pi(x+y)-\pi(x)\le\frac{2y}{\log y+1.1328}\qquad (x\ge0,\ y\ge e^{70}). \tag{1}
\]
The [192-bit Arb verifier](correlated_farey.py) checks the numerical parts. The new ingredient in (1) is the joint, reflected distribution of the two Farey-neighbor denominators.

## Correlation of the two neighbors

Retain \(C=4/3,\ N=\lceil y\rceil+1\). Write \(k=1.045,\ g=k^2,\ z=k\sqrt{N/C}\), and \(z_0=k\sqrt{e^{70}/C}\). Apply the [weighted large sieve argument](../../round3/low/FAREY.md) with this Farey order \(z\). The result there, valid also for this choice of order, bounds the number of primes exceeding \(z\) in the interval by \(N/\mathcal H\), where
\[
 \mathcal H=\sum_{q\le z}\frac{\mu^2(q)}{\varphi(q)(1+C M_q/N)}.
\]
Here \(M_q\) is the mean inverse nearest-neighbor spacing over reduced fractions with denominator \(q\). Always \(M_q\le qz\). The two individual neighbors have determinants \(+1,-1\) as in the earlier proof. [Preissmann, inequalities (B) and (D)](https://www.e-periodica.ch/cntmng?pid=ens-001%3A1984%3A30%3A%3A30) · [Montgomery–Vaughan, (1.6)–(1.8)](https://doi.org/10.1112/S0025579300004708).

For squarefree \(q\ge z/256\), let \(r\) run through the reduced residues divided by \(q\). The two neighbor denominators are the largest integers \(\le z\) in opposite invertible residue classes modulo \(q\). Their two deficits from \(z\), divided by \(q\), are
\[
 x_r=\{z/q-r\},\qquad y_r=\{z/q+r\}=\{\lambda-x_r\},
 \qquad \lambda=\{2z/q\}.
\]
Inverse residue classes range over all reduced residues, so \(M_q=q(z-q\,\mathbb E_r\min(x_r,y_r))\).

For uniform real \(x\in[0,1]\),
\[
 \int_0^1\min(x,\{\lambda-x\})\,dx
   =\frac{\lambda^2}{4}+\lambda(1-\lambda)+\frac{(1-\lambda)^2}{4}
   =\frac14+\frac{\lambda(1-\lambda)}2. \tag{2}
\]
Split at \(\lambda\) to obtain the first equality. Each strict upper level set of the minimum is the complement of the union of two arcs, so is the union of at most two circle intervals. For a single arc, the normalized counting error for the translated reduced residues is at most \(D_q=2^{\omega(q)}/\varphi(q)\) by inclusion–exclusion. Arcs crossing the seam can be lifted as single intervals since the residues are periodic; any endpoints at an equality affect a null set of levels. Integrating the pointwise discrepancy over the possible levels \([0,1]\) proves
\[
 M_q\le q(z-qD),\qquad
 D=\frac14+\frac{\lambda(1-\lambda)}2-2D_q,\qquad
 D_q\le\sqrt{30/q}.
 \tag{3}
\]
The last inequality follows from \(\sqrt q D_q=\prod_{p\mid q}2\sqrt p/(p-1)\) and only the factors at \(2,3,5\) exceeding one.

## Summing the improvement over all denominators

Write \(G(t)=\sum_{q\le t}\mu^2(q)/\varphi(q)=\log t+c_0+E(t)\), where \(1.33258<c_0<2,\ |E(t)|\le 2.44/\sqrt t\) for \(t>1\). [Ramaré, Theorems 1.3 and 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/113104).

The baseline \(\mathcal H_0\) uses \(M_q\le qz\) in every term and hence sieve weight \(1/(1+g q/z)\). Partial summation gives the contribution from \(\log t+c_0\) as
\[
 \log z-\log(1+g)+\log(1+g/z)+c_0/(1+g/z).
\]
Indeed the weight times \(c_0\) at 1 gives the last term and the derivative \(1/t\) yields the other three. The endpoint and integrated remainder together cost at most \(2.44(1+2g)/\sqrt z\). Use \(c_0/(1+g/z)\ge c_0-2g/z\). Thus
\[
 2\mathcal H_0-\log N\ge
 2(1.33258)-\log C+2\log k-2\log(1+g)
       -4g/z_0-2(2.44)(1+2g)/\sqrt{z_0}.                             \tag{4}
\]

Partition \(u=q/z\in(1/256,1]\) into cells \((a,b]=(i/m,(i+1)/m]\), \(m=16384\). In each cell put
\[
 D_i=\tfrac14+\tfrac12\min_{a\le v\le b}\{2/v\}(1-\{2/v\})
              -2\sqrt{30/(z_0a)} .
\]
For cells containing an integer value of \(2/v\), use zero for the minimum. In each other cell concavity of \(w(1-w)\) gives the minimum at an endpoint. The verifier detects the integer crossings with exact integer division and computes the endpoint residues from exact remainders. It verifies \(0<D_i<1\). Discard the improvement below or at \(u=1/256\), retaining its whole baseline.

Equation (3) improves the sieve weight in this cell by at least
\[
 f_i=\frac{gD_i a^2}{(1+ga)(1+ga-gD_i a^2)}.
\]
Indeed the same expression with \(u\) in place of \(a\) equals \(gD_i[u/(1+gu)]^2/[1-gD_i u^2/(1+gu)]\), increasing on the cell with positive denominator. The improvement to \(\mathcal H\) is therefore at least \(\sum_i f_i(G(zb)-G(za))\). Adjacent endpoint errors telescope with may-be-signed differences of consecutive \(f_i\). Writing \(f_{\rm prev}=0\) at the first cell, the sum is bounded below by
\[
 \sum_i f_i\log(b/a)
 -\frac{2.44}{\sqrt{z_0}}
  \left(f_{\rm last}+\sum_i |f_i-f_{\rm prev}|/\sqrt a\right).
\]
Adding this twice to (4) proves \(2\mathcal H>\log N+1.1328444135\) uniformly. As \(k<\sqrt C\), the small-prime allowance \(z\le2\sqrt y\) and \(N\le y+2\) give exactly the same length conversion as in the previous proof. The quantity \(2(u+2)e^{-u}+(u+2)^2e^{-u/2}\) decreases and is below \(0.00004\) for \(u=\log y\ge70\). This proves (1).

## Fourth-power coverage

In the [signed compact-frequency proof](../../round2/local/EDGE.md) use \(\eta=1.1328\). Its smallest primary tangent scale is \((2\pi-2a)/512>1/256\), where here \(a\) denotes the signed kernel parameter. All tangent scales are at most 7. Even though (1) is asserted only for \(y\ge e^{70}\), every tangent intercept exceeds \(e^{70}+1\) since
\[
 \frac{2e^{115}}{256(H+300000)120^2}>e^{70}+1,\qquad H=3\,000\,175\,332\,800.
\]
For shorter lengths direct integer counting therefore suffices. The remaining terms of the explicit formula are unchanged. The verifier gives the following strict upper bounds, including both endpoints of every cell.

| \(L\) interval | \(K-H\) | normalized error below | last \(n\) |
|---|---:|---:|---:|
| \([115.032114,115.03329]\) | \(-1\,280\,000\) | \(0.999983737\) | 3,087,313,774,153 |
| \([115.03329,115.033338]\) | \(-1\,280\,000\) | \(0.999999814\) | 3,087,350,822,141 |
| \([115.033338,115.033340]\) | \(300\,000\) | \(0.999999724\) | 3,087,352,365,817 |

The last row uses QRH above \(H\). The first two use the verified RH interval and an unconditional Gaussian tail. Reproduce with \(\texttt{python -B correlated_farey.py}\). This is a written proof with interval arithmetic, without a Lean formalization. Project attribution to Claude and Codex. Codex derived the correlated-neighbor sieve and its interval transfer.
