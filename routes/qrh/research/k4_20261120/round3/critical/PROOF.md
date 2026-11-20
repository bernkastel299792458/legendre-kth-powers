# An explicit fourth-moment upper bound from the moving Riemann–Siegel sum

For every \(T\ge e^{54}\), the phase estimate below gives
\[
 \int_0^T|\zeta(1/2+it)|^4\,dt < 0.087023\,T\log^4 T .
\]
For \(T\ge e^{56}\) the constant is \(0.086382\). A version using absolute values throughout gives \(0.146564\) and \(0.144789\), respectively. Both estimates use the explicit Riemann–Siegel remainder and apply to the BV mollifier boundary. The arithmetic and analytic arguments are written proofs with Arb scalar verification.

## Moving cutoff

For \(t\ge200\), put \(D(t)=\sum_{n\le\sqrt{t/(2\pi)}} n^{-1/2-it}\). The explicit Riemann–Siegel inequality gives
\[
 |\zeta(1/2+it)|\le 2|D(t)|+1.48 t^{-1/4}+.127t^{-3/4}
                  \le 2|D(t)|+2t^{-1/4}.
\]
On \(0\le t\le200\), Euler summation at 1 bounds \(|\zeta(s)|\le |s/(s-1)|+|s|/\Re s\le403\). [Hiary, Lemma 2.1](https://www.sciencedirect.com/science/article/am/pii/S0019357715000865), [Yang, equation (3.1)](https://doi.org/10.1016/j.jnt.2024.03.011).

Fix \(T\ge e^{20}\), \(Y=\sqrt{T/(2\pi)}\), \(N=Y^2\), \(v=\log Y\), and let \(a_n=\#\{(j,k)\in\mathbb N^2: j,k\le Y,\ jk=n\}\). In the expansion of \(|D(t)|^4\), each quadruple has a time interval \([\max(200,2\pi\max_i n_i^2),T]\), possibly empty. A diagonal integral has length at most \(T\). Every off-diagonal integral with products \(m<n\) has modulus at most \(2/\log(n/m)\), regardless of its lower endpoint. Both orientations give
\[
 \int_{200}^T |D(t)|^4dt
 \le T\sum_n a_n^2/n
      +4\sum_{m<n}\frac{a_ma_n}{\sqrt{mn}\log(n/m)} .                 \tag{1}
\]

For \(m<n\), \((\sqrt{mn}\log(n/m))^{-1}\le(n-m)^{-1}+(2\sqrt{mn})^{-1}\). In fact for \(t=\log(n/m)>0\) this follows from \(1/t-1/(2\sinh(t/2))\le1/t-1/(e^t-1)\le1/2\), using \(\tanh(t/2)\le t/2\). For each \(k\ge1\), Cauchy–Schwarz gives \(\sum_n a_na_{n+k}\le\sum a_n^2\). Also \(\sum a_n/\sqrt n=(\sum_{j\le Y}j^{-1/2})^2\le4Y\).

The equality \(ab=cd\) with all four indices at most \(Y\) has a unique representation \(a=gr,\ c=gs,\ b=hs,\ d=hr,\ (r,s)=1\). Therefore
\[
 \sum a_n^2=\sum_{(r,s)=1}\lfloor Y/\max(r,s)\rfloor^2
       \le 2 Y^2(1+\log Y).
\]
Combining the last three estimates yields the following bound on the whole off-diagonal term of (1),
\[
 \frac T{2\pi}\big[8(1+v)(1+2v)+16\big].                          \tag{2}
\]
Here the restriction of both factors of a product to \([1,Y]\) enters the unweighted energy.

## Diagonal energy

Write \(H_x=\sum_{j\le x}1/j\), including \(H_x=0\) for \(x<1\). The same parametrization gives
\[
 \sum_n a_n^2/n
   =\sum_{(r,s)=1}\frac{H_{Y/\max(r,s)}^2}{rs}.
\]
Take \(P=2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17\cdot19\). For each \(z\ge1\), inclusion–exclusion and positivity show that the weighted count of coprime pairs \(r,s\le z\) is at most
\[
 \sum_{d\mid P}\frac{\mu(d)}{d^2}H_{z/d}^2\le b\log^2 z+c\log z+c_0,
\]
where \(b=\sum_{d\mid P}\mu(d)/d^2,\ c_0=\sum_{\mu(d)=1,\,d\mid P}1/d^2\) and \(c=2c_0+2\sum_{\mu(d)=-1,\,d\mid P}(\log d)/d^2\). For positive coefficients use \(H_{z/d}\le1+\log z\). For negative coefficients use \(H_{z/d}^2\ge(\log(z/d))_+^2\ge\log^2z-2\log z\log d\). Thus this polynomial applies also when \(z<P\).

Bound \(H_{Y/\max(r,s)}^2\le(1+\log[Y/\max(r,s)])^2\) and partially sum the coprime count. Writing \(B(v)=bv^2+cv+c_0\), this yields
\[
 \sum_n a_n^2/n \le
 Q(v)=B(v)+2\{b(v^3/3+v^4/12)+c(v^2/2+v^3/6)+c_0(v+v^2/2)\}.
                                                                    \tag{3}
\]
The term \(B(v)\) is the upper boundary and the integral is \(2\int_0^v B(x)(1+v-x)\,dx\). In particular the contributions from \(r=s=1\) and harmonic endpoints are included.

## Full height range and use on the critical line

Write \(u=\log T\), \(U\le u\), \(v=(u-\log(2\pi))/2\). Let
\[
 Q(v)+[8(1+v)(1+2v)+16]/(2\pi)=\sum_{j=0}^4 p_j u^j,\qquad
 E(U)=\sum_{j=0}^4 \max(0,p_j)U^{j-4}.
\]
Equations (1)–(3) then give \(\int_{200}^T |D|^4\le E(U)Tu^4\). Including the two disjoint error ranges by the \(L^4\) triangle inequality gives the uniform coefficient
\[
 C(U)=\left[2E(U)^{1/4}
       +\frac1U\big\{200\cdot403^4e^{-U}+16Ue^{-U}\big\}^{1/4}\right]^4.
\]
Indeed the fourth-power remainder above 200 contributes at most \(16\log T\) to its own integral, and \(u e^{-u}\) decreases for \(u>1\). The function \(\texttt{fourth_constant}(U)\) in the [Arb implementation](rs_fourth.py) returns this upper bound for all \(T\ge e^U\), \(U\ge20\).

For the BV rational weight of [the spectral proof](../../round2/spectrum/PROOF.md) use \(C_4=C(U)v_0^{1+4/U}m/(m-1-4/U)\), with the published project choices \(m=2048,\ v_0=1.01\). Integrating against the negative derivative of the rational window's real majorant gives the stated multiplier. The same Hölder and triangle inequalities as in the spectral proof now give
\[
 K_1=\left[C_4^{1/4}C_M^{1/2}+\bar y^{3/4}U^{-3/2}\right]^{4/3},
 \qquad \bar y=v_0m/(m-1).
\]
The function \(\texttt{left_endpoint}(U,W,\log h_0)\) uses the former BV estimate for \(C_M\). Alternatively \(C(U)\) can be used with any independently established \(C_M\) for the same mollifier and window.

## Harmonic numbers with their constant term

Write \(\gamma\) for Euler's constant, \(H_y=\sum_{n\le y}1/n\) and \(u=\log z\). For \(z,d\ge1\), \(y=z/d\),
\[
 \big|H_y^2-(\gamma+\log y)^2\big|
 \le (2u+2\gamma+1)/y .                                              \tag{4}
\]
For \(y\ge1\), \(n=\lfloor y\rfloor\), the integral comparison defining Euler's constant gives \(0\le H_n-\log n-\gamma\le1/n\). The upper bound and the monotonicity of \(\log y+1/y\) give \(H_y\le\log y+\gamma+1/y\). The lower bound for \(H_{n+1}\) gives \(H_y\ge\log(n+1)+\gamma-1/(n+1)\ge\log y+\gamma-1/y\). Squaring and using \(0\le\log y\le u\) gives (4). If \(y<1\), set \(v=-\log y\). Then \(H_y=0\) and \((\gamma-v)^2\le\max(\gamma^2,v^2)\le e^v\).

Use the same \(P\) and \(b\) as in (3), and now set
\[
 c=2\sum_{d\mid P}\frac{\mu(d)(\gamma-\log d)}{d^2},\qquad
 c_0=\sum_{d\mid P}\frac{\mu(d)(\gamma-\log d)^2}{d^2},\qquad
 h=\sum_{d\mid P}\frac1d .
\]
After applying (4) separately to each sieve term, the harmonic count \(C(z)=\sum_{r,s\le z,\,(r,s)=1}1/(rs)\) satisfies
\[
 C(z)\le bu^2+cu+c_0+h e^{-u}(2u+2\gamma+1).                       \tag{5}
\]
In the diagonal identity preceding (3), replace \(H_{Y/\max(r,s)}^2\) by \((\gamma+\log[Y/\max(r,s)])^2\). For its error use the \(y\ge1\) case of (4) with \(z=y=Y/\max(r,s)\). After dropping the coprimality constraint, the pairs with \(\max(r,s)=k\) have mass at most \(2(1+\log Y)/k\). Their summed error is at most \(2(1+\log Y)(3+2\gamma)\), since \(\sum_{k\le Y}\log(Y/k)\le \int_0^Y\log(Y/t)\,dt=Y\).

Let \(\ell=\log Y\), \(B(u)=bu^2+cu+c_0\). Partial summation with the remaining weight gives the polynomial
\[
 Q_*(\ell)=\gamma^2 B(\ell)+2\int_0^\ell B(u)(\gamma+\ell-u)\,du
          +\gamma^2h(2\ell+2\gamma+1)+2h(\ell+\gamma)(3+2\gamma)
          +2(1+\ell)(3+2\gamma).
\]
The boundary error follows from \(e^{-\ell}\le1\). The integral error uses \(\int_0^\infty e^{-u}(2u+2\gamma+1)\,du=3+2\gamma\). Thus \(Q_*\) bounds the diagonal in (1). Define \(E_*(U)\) as for \(E(U)\), using \(Q_*\) in place of \(Q\).

## The fourth harmonic of the Riemann–Siegel sum

Let \(\vartheta_0(t)=(t/2)\log(t/(2\pi e))-\pi/8\) and \(z(t)=e^{i\vartheta_0(t)}D(t)\). The cosine form of the Riemann–Siegel estimate gives \( |\zeta(1/2+it)|\le2|\Re(e^{i\vartheta(t)}D(t))|+2t^{-1/4}\). For \(t\ge200\), the theta expansion gives \(|\vartheta(t)-\vartheta_0(t)|\le(1+\pi)/(48t)+\arctan(e^{-\pi t})/2<1/t\). Since \(|D(t)|\le2t^{1/4}\) and \(4t^{-3/4}\le t^{-1/4}\),
\[
 |\zeta(1/2+it)|\le2|\Re z(t)|+3t^{-1/4}.
\]
The published cosine inequality is needed here. [Hiary, equation (11)](https://www.sciencedirect.com/science/article/am/pii/S0019357715000865), [Brent, Theorems 5 and 6](https://maths-people.anu.edu.au/~brent/pd/rpb268v2.pdf).

For fixed four indices \(n_i\le Y\) in \(z^4\), write \(m=\max n_i\) and \(j=\min n_i\). The phase \(\Phi(t)=4\vartheta_0(t)-t\log\prod n_i\) is integrated from \(\max(200,2\pi m^2)\) to \(T\). Throughout this interval \(\Phi'(t)=2\log(t/(2\pi))-\log\prod n_i\ge\log(m/j)\) and \(\Phi'\) increases. If \(\Phi'\ge\lambda>0\), integration by parts gives \(|\int e^{i\Phi(t)}dt|\le 2/\lambda\), including both boundary terms and the variation of \(1/\Phi'\).

When \(j=m\), use the interval length \(T\) and sum \(T\sum_{m\ge1}m^{-2}<2T\). When \(j\le m/2\), use \(2/\log 2\) and sum weights at most \((\sum_{n\le Y}n^{-1/2})^4\le16Y^2\). For the remaining tuples set \(r=m-j\), so that \(1\le r<m/2\). The integral is at most \(2m/r\), and its weight is at most \(4/m^2\). Fixing one position for \(m\) and another for \(j\) bounds the count by \(12(r+1)^2\le48r^2\). The sum at fixed \(m\) is at most \(384m^{-1}\sum_{r<m/2}r\le192m\). Summing \(m\) gives at most \(192Y^2\). Thus
\[
 \left|\int_{200}^T z(t)^4\,dt\right|
 \le 2T+(32/\log 2+192)Y^2<64T.                                    \tag{6}
\]

Set \(B_4=\int_{200}^T|z|^4\le T\log^4(T)E_*(U)\). Then \(\int(\Re(z^2))^2=(B_4+\Re\int z^4)/2\). Using \((2\Re z)^2=2|z|^2+2\Re(z^2)\), the \(L^2\) triangle inequality gives
\[
 \left(\int_{200}^T|2\Re z|^4\right)^{1/2}
 \le 2\left(\sqrt{B_4}+\sqrt{(B_4+64T)/2}\right).
\]
The two disjoint error ranges contribute at most \(200\cdot403^4+81\log T\) to their fourth-power integral. One more \(L^4\) triangle inequality gives the uniform fourth-moment coefficient returned by \(\texttt{fourth_constant}(U,\texttt{phased=True})\),
\[
 \left[
 \left\{2\left(\sqrt{E_*(U)}+\sqrt{(E_*(U)+64/U^4)/2}\right)\right\}^{1/2}
 +\frac{[(200\cdot403^4+81U)e^{-U}]^{1/4}}{U}
 \right]^4 .
\]

## Integration of the diagonal and counting shifted products

At time \(t\ge200\), every term of the diagonal is active precisely when its four indices are at most \(\sqrt{t/(2\pi)}\). Its total contribution to the integral is at most \(\int_{200}^T q(\log t)\,dt\), where \(q(u)=Q_*((u-\log(2\pi))/2)\). If \(F=q-q'+q''-q'''+q''''\), then \((tF(\log t))'=q(\log t)\). After division by \(T\), a uniform upper bound for \(T\ge e^U\) is \(F(\log T)+\max(0,-200F(\log200))e^{-U}\). This is the polynomial used with the averaged option.

For an integer \(k\ge1\), the correlation \(\sum_n a_n a_{n+k}\) counts products \(ab-cd=k\) with the four factors at most \(Y\). For fixed \(a,c\), let \(g=(a,c)\). Solutions require \(g\mid k\), and their possible \((b,d)\) are spaced by the vector \((c/g,a/g)\). Thus each admissible \((a,c)\) contributes at most \(1+Yg/\max(a,c)\). The sum of the first terms is at most \(Y^2\). For the second terms at a fixed \(g\mid k\), drop coprimality and use
\(\sum_{r,s\le Y/g}1/\max(r,s)\le2Y/g\). The correlation is at most \(Y^2(1+2\sum_{g\mid k}1/g)\). Summing with weight \(1/k\) up to \(N\) costs at most \(Y^2(1+2\zeta(2))(1+\log N)\), since \(\sum_{g\le N}g^{-2} H_{N/g}\le\zeta(2)(1+\log N)\). Hence (2) can be replaced by
\[
 \frac{T}{2\pi}\left[4(1+2\zeta(2))(1+2\log Y)+16\right].
\]
The additional \(16\) pays for the second term of the kernel bound in (1). Using both refinements in (6) and its subsequent norm estimate gives the coefficient computed with the three options \(\texttt{phased=True, averaged=True, shifted=True}\). For \(U=54\) it is below \(0.079274472\). All shifted-product counts here concern the unmollified fourth moment on the critical line.
