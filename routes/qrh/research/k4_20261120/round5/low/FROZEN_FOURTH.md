# A finite integer Gram sum for the local critical fourth moment

This bound is used for the [short-interval density certificate](FINITE_POINTS.md). Put \(H=3000175332800,\ R=D/2,\ C=H+R,\ J=2(1.01)R\) and \(Y=\lfloor\sqrt{C/(2\pi)}\rfloor\). Assume \(C-J\geq200\), as the script checks in each application. At \(D=5\,000\,000\), \(Y=691008\). A new squarefree-divisibility computation gives \(8,964,635,410,982\) as an upper bound for the unweighted fourth-moment coefficient sum. The resulting bound on half of the full-axis \(G_C\)-weighted fourth moment of \(\zeta E_6\) is less than \(198.302H\). [Window arithmetic](frozen_fourth.py) · [Exact integer Gram sum](frozen_energy.py)

**Freezing the Riemann–Siegel cutoff.** Let \(D_Y(t)=\sum_{n\leq Y}n^{-1/2-it}\), \(y_0=\sqrt{C/(2\pi)}\), \(y_\pm=\sqrt{(C\pm J)/(2\pi)}\) and \(E_6(z)=(1-2^{-z})(1-3^{-z})\). The [explicit Riemann–Siegel inequality](../../round3/critical/PROOF.md), with [Hiary, Lemma 2.1](https://www.sciencedirect.com/science/article/am/pii/S0019357715000865), compares \(|\zeta(1/2+it)|\) with \(2|D_{\lfloor\sqrt{t/(2\pi)}\rfloor}(t)|\), at error at most \(2t^{-1/4}\) for \(t\geq200\). For \(|t-C|\leq J\), the two cutoffs differ by at most \(1+\max(y_+-y_0,y_0-y_-)\) indices, all greater than \(y_-\). Multiplying the resulting triangle inequality by \(|E_6|\) gives
\[
 |\zeta E_6|\leq 2|E_6 D_Y|+
  2(1+2^{-1/2})(1+3^{-1/2})
   \left[(1+\max(y_+-y_0,y_0-y_-))/\sqrt{y_-}+(C-J)^{-1/4}\right].
\]
Write the final term as \(e_0\). Time translation does not alter the lengths or absolute coefficients of the fixed Dirichlet polynomial.

**The unweighted norm.** Set \(N=6Y\) and
\[
 b(n)=\sum_{d\mid6}\mu(d)\,\mathbf1_{d\mid n,\; n\leq dY}.
\]
Then \(E_6 D_Y=\sum b(n)n^{-1/2-it}\). One has \(|b(n)|\leq1\): for each possible \((n,6)\) the included terms are a final segment of the ordered list of its divisors \(1,2,3,6\) with signs \(+,-,-,+\), restricting to the divisors of \((n,6)\). Each such final sum has modulus at most one. Let \(b*b\) be Dirichlet convolution. Expanding the equality of products \(ab=cd\) using \(a=km,c=kj,\ b=\ell j,d=\ell m,\ (m,j)=1\) gives the exact identity
\[
 E:=\sum_n (b*b)(n)^2
   =\sum_{(m,j)=1}\left(\sum_{k\geq1}b(km)b(kj)\right)^2.
\]
All terms on the far right are nonnegative. Restricting coprimality to the primes \(2,3,5,7\) gives an upper bound
\[
 E\leq\sum_{v\mid210}\mu(v)G_v,\quad
 G_v=\sum_{m,j\geq1}\left(\sum_{k\geq1}b(vkm)b(vkj)\right)^2.
\]
The inclusion-exclusion sum here computes the relaxed condition exactly, so the negative summands require exact values. The program uses signed integers.

Here is an efficient exact identity for \(G_v\). Define \(N_v=\lfloor N/v\rfloor,\ M=\lfloor\sqrt{N_v}\rfloor,\ K=\lfloor N_v/(M+1)\rfloor\), and let \(P_{ij}=\sum_k b(vik)b(vjk)\), \(P'_{ij}=\sum_{k\leq M} b(vik)b(vjk)\). Then
\[
 G_v=\sum_{i,j\leq M}P_{ij}^2+
                 \sum_{i,j\leq K}(P_{ij}^2-(P'_{ij})^2).
\]
To see this, the first term counts the part with \(i,j\leq M\). In its complement, at least one of \(i,j\) exceeds \(M\); both \(k,\ell\) in the expanded square must then be at most \(K\). Exchange \((i,j)\) with \((k,\ell)\), and subtract those original-index contributions for which both original indices were at most \(M\). This argument allows signed \(b\).

Every entry \(P_{ij}\) is the sum, over \(d,e\mid6\), of \(\mu(d)\mu(e)\) times
\[
 \left\lfloor\frac{\min(\lfloor dY/(vi)\rfloor,\lfloor eY/(vj)\rfloor)}
 {\operatorname{lcm}(d/(d,vi),e/(e,vj))}\right\rfloor .
\]
Minimizing the numerator additionally with \(M\) computes \(P'_{ij}\). The program uses symmetry to compute one triangle of each matrix. The largest intermediate entry in the signed construction is at most \(16N_v\), and a final entry is bounded by \(N_v\) since \(|b|\leq1\). In triangular row \(i\), each entry is bounded by \(N_v/i\) because \(b(vik)=0\) for \(k>N_v/i\). Hence twice its sum of squared entries is at most \(2N_v^2/i\). The script checks \(2N_v^2<2^{63}\) before the row dot products and uses arbitrary-precision Python integers for the final row aggregation and inclusion-exclusion. Thus this full two-matrix calculation has \(O(N_v)\) bounded-size integer operations per divisor \(v\), using row buffers of length \(O(\sqrt{N_v})\).

**Harmonic norm and integration.** Dropping signs and using the same coprime parametrization for the weighted norm gives
\[
 \sum_n (b*b)(n)^2/n
 \leq H_N^2+2\sum_{m=2}^N H_m H_{\lfloor N/m\rfloor}^2/m .
\]
Here \(H_j\) is the \(j\)-th harmonic sum. In each of 128 logarithmic bands \((e^\alpha,e^\omega]\) use \(H_m\leq1+\omega,\ H_{\lfloor N/m\rfloor}\leq1+\log N-\alpha\), and \(\sum 1/m\leq\omega-\alpha+e^{-\alpha}\). The latter follows by isolating the first term and integrating \(1/t\) over the remaining range. The script includes the separate \(H_N^2\) and one harmless spare unit; denote its upper bound by \(h_4\).

Apply the [complex-coefficient mean theorem, CS v2 Lemma 10 equation (49)](https://arxiv.org/html/2507.15184v2#S3) to \((E_6D_Y)^2\) on the symmetric interval of half-length \(J\) about \(C\). Its half-integral is bounded by
\[
 K=(J+c_0/2)h_4+c_0 E,\qquad
 c_0=\pi\sqrt{1+\tfrac23\sqrt{6/5}}.
\]
The time translation only changes phases. On \(|t-C|\leq J\) use \(G_C(t)\leq1\) and Minkowski: the half-integral of \(G_C|\zeta E_6|^4\) on this segment is at most \((2K^{1/4}+e_0 J^{1/4})^4\). For the complementary part the global fourth moment used in the [moving-window proof](MOVING_WINDOW.md) gives at most
\[
 C_* B\log^4 B\frac{2048}{2048-p}\,2^{p-2048},
 \quad B=C+1.01R,\qquad p=1+4/\log B.
\]
Indeed only interval radii at least \(2(1.01)R\) can reach the complement in the layer representation of \(G_C\); their whole mass can be charged using the same cumulative majorant, retaining both time signs. The program checks this last cost is below \(10^{-500}\). All sign changes of the frozen coefficient are handled before the time mean is estimated.

**A sharper harmonic Gram sum.** The expression preceding the coarse harmonic bound is, exactly,
\[
 \sum_{(i,j)=1}\frac1{ij}
       \left(\sum_{k\geq1}\frac{b(ki)b(kj)}k\right)^2 .
\]
Dropping the coprimality condition gives a positive upper bound. With \(v=1\) the same hyperbola interchange as in the integer computation applies with reciprocal weight \(1/(ijk\ell)\), since this weight is invariant under exchanging the two index pairs. Each squared Gram entry therefore gets its factor \(1/(ij)\). In its inner divisor-pair formula replace the count by \(H_{\lfloor z/m\rfloor}/m\), where \(z\) is the minimum cutoff and \(m\) is the least common multiple. For the truncated matrix also minimize \(z\) with \(M\). At \(Y=691008\) this sharper harmonic upper bound is less than \(202.894\).

Here are the directed-rounding details for the harmonic calculation in [frozen_energy.py](frozen_energy.py). Put \(L=2^{36},S=2^{16}\). Compute integer \(\widetilde H_n=\sum_{j\leq n}\lfloor L/j\rfloor\), so \(0\leq LH_n-\widetilde H_n<n\) for \(n\geq1\), with zero error at \(n=0\). If the signed divisor sum for an entry is built from \(\lfloor \widetilde H_{\lfloor z/m\rfloor}/m\rfloor\), its error relative to \(L\) times the exact entry is at most \(16(N+1)\). Round the computed absolute value outward at scale \(S\), then add or subtract \(\lceil16(N+1)S/L\rceil\) for upper or lower bounds. Clip the lower bound at zero. An upper charge is the ceiling of the upper integer squared divided by \(ij\); a lower charge uses floor. In counting each row twice less its diagonal, use the same upper (or lower) diagonal entry, so the symmetric sum contains it exactly once. Add the full upper rows and subtract only truncated lower rows. Divide the final Python integer by \(S^2\). All intermediate NumPy signed 64-bit products are checked against \(|\sum_k b(ki)b(kj)/k|\leq1+\log N\), the error allowances above and the actual row lengths. The integer calculation sieved at 2, 3, 5 and 7 and the harmonic calculation use independent upper bounds and retain both.

The [short-prefix estimate](prefix_fourth.py) can also replace the term \(J^{1/4}(1+\max(y_+-y_0,y_0-y_-))/\sqrt{y_-}\) in the Minkowski fourth root by a smaller fourth norm. The prefix on each half-window has one time interval of activity for each index, and thus for each fixed quadruple. Integrals for distinct product frequencies \(m,n\in[a^2,b^2]\) are at most \(\min(J,2b^2/|m-n|)\) before coefficient weights. For product counts \(r_m\), Cauchy gives \(\sum_m r_m r_{m+d}\leq\sum_m r_m^2\). The short interval product energy is counted by writing equal products as \(gr,hs,gs,hr\), as in the finite Gram proof. With \(r>s\) and unequal \(g,h\), \(r\leq b-a,\ 1\leq r-s\leq\lfloor r(b-a)/b\rfloor\), and \(g,h\) occupy an interval of width at most \((b-a)/r\). The function counts both orders, adds the trivial swaps, and integrates the scalar harmonic sum on nonzero shifts. The program retains the smaller of the uniform and fourth-mean prefix costs; the Riemann–Siegel remainder \(2(C-J)^{-1/4}\) is charged in both cases.
The complete next prime-interval slab is \(115.033675\leq\log x\leq115.034000\). The previous [translated-window slab](MOVING_WINDOW.md) reaches its left endpoint. Put \(K=H+1\,100\,000\,000\) and take eight equal height steps through \(K+1\,280\,000\); their anchored windows have exactly the centers and lengths in the argument above. All remaining prime and spectral terms are unchanged from that proof. The 192-bit sum is less than \(0.999994\). The complete single-slab replay, including all eight cumulative counts, both Gaussian tail bounds, prime powers and the ending integer, is:

~~~sh
python -B round5/low/frozen_cover.py
~~~
