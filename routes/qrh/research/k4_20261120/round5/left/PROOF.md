# A fourth moment retaining the residue and ratio of the gcd parameters

On \(s=1/2+it\), write \(E(s)=(1-2^{-s})(1-3^{-s})\). For \(T\ge e^U,\ U\ge20\), the routine \(\texttt{fourth}(U)\) bounds
\[
 \frac1{T\log^4T}\int_0^T|\zeta(s)E(s)|^4dt .
\]
At \(U=43\) its value is below \(0.012868529\). The Riemann–Siegel inequality, the treatment of its remainder and the estimate of unequal product frequencies come from the [previous proof](../../round4/density/SIEVED.md). We replace the equal-frequency contribution.

Set \(y=\sqrt{t/(2\pi)},\ \ell=\log y,\ d=1/3,\ A=\{n:(n,6)=1\}\) for \(t\ge200\). The filtered Riemann–Siegel Dirichlet polynomial has coefficients \(C(n)=C_{(n,6)}(n/y)\). The unit class has \(C_1(x)=\mathbf1_{x\le1}\). The other three functions are \(C_2=-\mathbf1_{1<x\le2},\ C_3=-\mathbf1_{1<x\le3},\ C_6=-\mathbf1_{1<x\le2}+\mathbf1_{3<x\le6}\).

Writing the variables of the equation \(ab=cd\) as \(a=gr,\ c=gs,\ b=hs,\ d'=hr\), with \((r,s)=1\), the exact diagonal at this time is
\[
 \sum_{(r,s)=1}\frac{1}{rs}
   \left(\sum_{g\ge1}\frac{C(gr)C(gs)}g\right)^2 .                 \tag{1}
\]
The equality uses the fact that the \(g,h\) ranges are independent and the coefficients real. We use symmetry to take \(s\ge r\), paying a factor 2 whenever the diagonal \(r=s\) has already been included.

## Products whose two indices are at most \(y\)

Put \(t_*=y/s\) temporarily. On \(g\le t_*\) the inner term is exactly \(\mathbf1_{r,s\in A}H_A(t_*)\), where \(H_A(x)=\sum_{g\le x,g\in A}1/g\). One has \(H_A(x)\le1+d\log x\) for \(x\ge1\) as in the previous proof. More precisely, with \(k=4/3\) and \(c=(\gamma+\log2+\frac12\log3)/3\),
\[
 |H_A(x)-d\log x-c|\le k/x\quad(x\ge1).
\]
Indeed the period-six count differs from \(dx\) by at most \(2/3\). The endpoint and integral errors in harmonic partial summation are each at most \(2/(3x)\). The constant follows by inclusion–exclusion applied to the ordinary harmonic asymptotic.

In the pure square of this term in (1), remove the coprimality restriction between two units. Replace the inner \(H_A(y/\max(r,s))^2\) by \((c+d\log(y/\max(r,s)))^2\). Its total error is bounded by \(2k(1+d\ell)(2d+2c+k)\), since the pair mass at maximum \(j\) is at most \(2(1+d\ell)/j\) and \(\sum_{j\le y}\log(y/j)\le y\). The external cumulative pair mass at \(e^u\) is \(H_A(e^u)^2\), bounded by \((du+c)^2+k e^{-u}(2du+2c+k)\). Partial summation with the smooth weight now contributes
\[
 c^2(d\ell+c)^2+2d\int_0^\ell(c+d(\ell-u))(du+c)^2\,du .
\]
Its external boundary error costs \(c^2 k(2d\ell+2c+k)\). Its integral error costs \(2dk(c+d\ell)(2d+2c+k)\), from integrating the decreasing exponential on the positive line. These are the three additional terms in \(\texttt{bulk}\).

## Tail of the inner harmonic sum

For \(h\in\{1,2,3,6\}\), let \(R_h=\{a:1\le a\le6,\ (a,6)=h\}\), \(\rho_h=|R_h|/6,\ c_h=\sum_{a\in R_h}1/a\). Let \(T_h(t)=\sum_{g>t}|C_{(hg,6)}(g/t)|/g\), and define \(F_h(t)=\sum_{g>t,\,g\in A}C_{(hg,6)}(g/t)/g\). The script bounds \(T_h\) by \(B_h\), \(|F_h|\) by \(L_h\), and \(|F_h(t)|\) for \(t\ge48\) by \(l_h\). For \(t\le48\) the sums are step functions, and all jumps at rational endpoints \(n/a,\ n/b\) are accumulated exactly as fractions for each interval \((a,b]\). The new value is attained at the jump, with the previous value already included. For \(t\ge48\) each single residue and band \(at<g\le bt\) contributes \(\log(b/a)/6\) with error at most \(1/(48a)\). This follows by partial summation from discrepancy at most 1 on intervals. The signs are retained in \(F_h\). The resulting \(B_h\) are bounded by \(1,4/3,3/2,11/6\), respectively.

In the range \(s/6<r\le s\), drop the restrictions on \(gr\) in the tail. Its contribution inside the square in (1) has absolute value at most \(B_h,\ h=(s,6)\). For \(X=\mathbb N\) or \(X=A\), let \(\rho_X=1\) or \(d\) and put
\[
 e_{X,h}=\sum_{(s,6)=h}\frac1s
     \left[\sum_{s/6<r\le s,\ r\in X}\frac1r-\rho_X\log6\right]_+ .
\]
The script sums this expression through 384. The remaining portion is bounded by \(6D_X/384\), with \(D_{\mathbb N}=1,\ D_A=2\), again by partial summation and \(\sum_{s>384}s^{-2}\le1/384\). The outer harmonic mass in class \(h\) through \(6y\) is bounded by \(H_h=c_h+\rho_h\log(6y)\), using the integral in each progression after its first entry. Thus the squared tail costs at most \(2\sum_h B_h^2\{(\log6)H_h+e_{\mathbb N,h}\}\) in this range. The cross term requires both \(r,s\in A\) and \(s\le y\). Its cost is at most
\[
 4B_1\left[
 d\log6\{1+d\ell+d(\ell+d\ell^2/2)\}+(1+d\ell)e_{A,1}
 \right].
\]
Here \(\sum_{s\le y,s\in A}H_A(y/s)/s\le H_A(y)+d\int_0^\ell H_A(e^u)du\), using the elementary harmonic upper bound on the inner factor.

In the other range \(s\ge6r\), any contributing \(g\) has \(gs\le6y\), hence \(gr\le y\). This forces \(r,g\in A\). If \(s\in A\), the inner sum has no tail. Otherwise the inner sum is exactly \(F_h(y/s)\), and has no bulk part. For \(s\le y/48\) use \(l_h\); for \(s>y/48\) use \(L_h\). On \((y/48,6y]\) the harmonic mass of class \(h\) is at most \(c_h+\rho_h\log(288)\), by the integral in each progression from the first admitted entry. Also \(H_A(s/6)\le1+d\log(6y)\) whenever \(s\ge6\). The far contribution is therefore at most
\[
 2(1+d\log(6y))\sum_{h>1}
     [l_h^2 H_h+L_h^2(c_h+\rho_h\log(288))].
\]
This expression allows the larger tail range to be counted twice, with nonnegative weights. The pure square, close costs and far costs form one polynomial in \(\log y\). Integrate this polynomial over the actual time interval and add the previously established off-diagonal and Riemann–Siegel remainder using the same [uniform scalar normalization](../../round4/density/sieved_fourth.py). Run **python -B six_energy.py** to reproduce the quoted coefficient.
