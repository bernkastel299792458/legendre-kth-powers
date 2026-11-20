# Two local zero counts on the smallest true rectangle

Assume every nontrivial zeta zero satisfies \(\beta\le\Theta=7/8\). By the functional equation, \(\beta\ge1-\Theta\). Put \(H=3000175332800\), \(T=H\exp(7/4)\), \(s=.865\). In \([H,T]\) every closed interval of length **.15** contains at most **two** zeros with \(\beta\ge s\), counted with multiplicity. In every closed interval of length **.28** there are at most **three**. Thus failure of the [second true count](../../round6/reduction/OBSTRUCTION.md) forces at least **210036** ordinates with mutual distance \(>.15\), and also at least **140024** with mutual distance \(>.28\). In each case select every second or every third zero in the ordered list, beginning with the first.

The integral inequalities below also give tests specific to the right boundary. No global zero count at the level \(420070\) is proved here. The existing simultaneous population example can still be placed equally spaced within each of its disjoint \(10^9\)-wide supporting intervals. Its largest population has \(3\cdot10495930\) points, leaving a spacing greater than 31. Thus imposing these two local count bounds alone still permits the example. The additional [cubic prime-polynomial bound](INCREMENT.md) excludes its original narrow support and forces any failure to span more than 116,000,000 in height.

## Positive kernels at the boundary

For \(A>0,\ a\ge0\), write
\[
 K_A(a,y)=\int_0^A (1-u/A)e^{-au}\cos(yu)\,du
 =\Re\left(\frac1z+\frac{e^{-Az}-1}{Az^2}\right),\qquad z=a+iy.
\]
The integral supplies the removable value at \(z=0\). This kernel is nonnegative on the **whole** closed half-plane \(a\ge0\). At \(a=0\) it is \(A\,\operatorname{sinc}^2(Ay/2)/2\), where \(\operatorname{sinc}(u)=\sin u/u\). For \(a>0\) it is its convolution with the probability density \(P_a(y)/\pi\), \(P_a(y)=a/(a^2+y^2)\). For \(0\le y\le\pi/A\), \(K_A(a,y)\) decreases in \(y\) by differentiation under the integral. It decreases in \(a\) there too: pair \(u\) with \(A-u\) in the derivative. The factor \(u(1-u/A)\) is symmetric. The earlier cosine is nonnegative and at least the absolute value of any negative later cosine, since \(\cos(yu)+\cos(y(A-u))\ge0\). The earlier exponential is the larger one.

Let \(b_0=\Theta-1/2\), and apply the Guinand–Weil formula to the translated entire function \(h(v)=\int_0^A(1-u/A)e^{-b_0u}\cos((v-t)u)\,du\). Its Fourier transform with the \(e^{-2\pi i v\xi}\) convention is \(\pi(1-|2\pi\xi|/A)_+e^{-b_0|2\pi\xi|}e^{-2\pi it\xi}\), and it decays quadratically in each fixed horizontal strip. For an individual zero, the real part of \(h((\rho-1/2)/i)\) is the average of the kernels at \(a=\Theta-\beta\) and \(a=\Theta-(1-\beta)\). Consequently the real zero sum, by reflection about the critical line, equals \(\sum_\rho K_A(\Theta-\beta,t-\gamma)\). The prime term is \(-P_A(t)\), where
\[
 P_A(t)=\sum_{n\le e^A}\Lambda(n)n^{-\Theta}(1-\log n/A)\cos(t\log n).
\]
The explicit formula is unconditional. Positivity of **every** term on this boundary requires QRH. The source formula for an even test also suffices, since replacing \(h(v)\) by \([h(v)+h(-v)]/2\) leaves the sum and the gamma integral invariant by the zero symmetry and real-part extraction. See [Chirre and Gonçalves, Proposition 5](https://doi.org/10.1007/s00209-021-02820-9).

Uniformly for \(8\le A\le120,\ H-1\le t\le T+1\), we obtain
\[
 \sum_\rho K_A(\Theta-\beta,t-\gamma)
 \le \tfrac12\log(t/(2\pi))+.0001-P_A(t). \tag{1}
\]
Here are details of the numerical archimedean error. The density in the gamma integral is \(K_A(b_0,y)/\pi\), of mass one, with the prefactor \(1/2\). For \(|y|\ge1\),
\(K_A(b_0,y)\le(b_0+2/A)/y^2\le1/y^2\).
Euler summation of \(\psi(z)=\lim_{n\to\infty}(\log n-\sum_{k=0}^{n-1}1/(z+k))\) gives \(|\psi(z)-\log z|\le\int_0^\infty|z+x|^{-2}dx\) for \(\Re z>0\) by comparing the sum term by term to its integral. This is at most \(\pi/(2|\Im z|)\) or \(1/\Re z\). Consequently for \(D=H/10000,\ |y|\le D\), \(\Re\psi(1/4+i(t+y)/2)\) exceeds \(\log(t/2)\) by at most \(\log(1+(D+1)/(H-1))+4/(H-1-D)\). For the tail use \(\Re\psi(z)\le\Re\psi(z+1)\le \log(2+|t+y|)+1\) at the stated \(z\), then \(\log(2+|t+y|)\le\log(T+3)+\log(1+|y|)\). Integrating with \(1/y^2\) gives the contribution to the average before its factor \(1/2\) of at most \(2[\log(T+3)+\log(1+D)+3]/(\pi D)\); dropping the subtracted \(\log(t/2)>0\) only increases the bound. The two polar terms involve \(K_A(-1/8,t)\) and \(K_A(7/8,t)\) by the same analytic formula, and their combined upper absolute bound is \(2[1+(1+\exp(15))/8]/(H-1)^2\). The resulting total is less than .000051.

## Prime-power phases and a compensated positive kernel

For \(A=10,\ |y|\le.14\), a right zero with \(\beta\ge s\) and its left partner give at least \(K_A(.01,.14)+K_A(.75,.14)\), by monotonicity. Write \(v_k=\log p\cdot p^{-k\Theta}(1-k\log p/A)_+\). For each prime, the joint lower bound on its first two cosine terms is the minimum of \(v_1 x+v_2(2x^2-1)\) on \([-1,1]\). Bound the remaining prime powers in absolute value. The finite calculation gives \(-P_{10}(t)<6.510345\) uniformly. Dividing the right of (1) by the indicated pair lower bound gives less than \(3.972155\) at these heights.

For the narrower interval take \(c=1.4,\lambda=.46\). For \(0\le a\le.375,\ b=.75-a,\ g=c-\Theta\), the following holds for every \(y\):
\[
 K_{10}(a,y)+K_{10}(b,y)
 \ \ge\lambda\,[P_{g+a}(y)+P_{g+b}(y)]. \tag{2}
\]
For \(|y|\le.30\) use the monotonicity already proved and the upper bound \(1/g+1/(g+.375)\) on the sum of Poisson kernels. For the rest set \(r=1/|y|\in[0,10/3]\). The explicit kernel formula bounds \(y^2K_A(a,y)\) from below by the maximum of zero and
\[
 \frac a{1+v}+\frac{1-v}{A(1+v)^2}
       -\frac{e^{-Aa}}{A(1+v)},\qquad v=(ar)^2.
\]
Meanwhile \(y^2P_k(y)=k/(1+(kr)^2)\). The verifier certifies (2) on the compact rectangle by 206 interval cells, split only when their lower bound does not already suffice. The real symmetry also covers both signs of \(y\) and both orders of \(a,b\). On-line zeros can be assigned half a duplicate pair.

Subtract \(\lambda\sum_\rho P_{c-\beta}(y)\) at \(y=t-\gamma\) from the two sides of (1). Hadamard factorization of the completed zeta, with its real constant canceled by symmetry about real part \(1/2\), identifies the Poisson sum with \(\Re\xi'/\xi(c+it)\). Its archimedean part \(\Re[1/(c+it)+1/(c-1+it)+\psi((c+it)/2)/2]-(\log\pi)/2\) differs from \(\tfrac12\log(t/(2\pi))\) by less than \(10^{-8}\), by the Euler estimate above. The signed combined prime coefficients are
\[
 v_k=\log p\,\left[p^{-k\Theta}(1-k\log p/10)_+-\lambda p^{-kc}\right].
\]
The verifier initializes the absolute cost of the subtracted series to \(-\lambda\zeta'(c)/\zeta(c)\). For \(p^k\le e^{10}\) it removes that cost and uses the joint finite coefficient; it again minimizes the quadratic in \(\cos(t\log p)\) for the first two powers. The combined prime upper bound is \(5.808617\). Every reflected pair has nonnegative excess by (2). For \(\beta\ge s,\ |y|\le.075\), its excess is at least
\[
 K_{10}(.01,.075)+K_{10}(.75,.075)
 -\lambda[1/(c-\Theta)+1/(c+s-1)] .
\]
The upper bound divided by this lower bound is \(2.990379\) or less. These counts hold even if the two horizontal endpoints are occupied.

## Positive-part moment at a zero-free line

Let \(c_*=.8751,\ a_0=c_*-s=.0101\), and \(B=\tfrac12\log(T/(2\pi))+.0001\). Failure of the second true count forces, for example,
\[
 \left(\frac{\int_{H-1}^{T+1}[\Re(\zeta'/\zeta)(c_*+it)]_+^{16}\,dt}
 {T-H+2}\right)^{1/16}>20.66 .
\]
The corresponding thresholds for powers \(8,12,20,24\) are \(5.20,13.01,27.32,32.95\), respectively. An upper bound at any one of these thresholds would settle the second rectangle.

Indeed, for each counted zero put \(a=c_*-\beta\in[.0001,.0101]\), \(b=c_*+\beta-1\). For \(t=\gamma+az,\ |z|\le2.8\), the two Poisson kernels give \(1/[a(1+z^2)]+P_b(az)\) with \(P_b(az)>1.30\). The completed logarithmic derivative identity and QRH give \(\Re(\zeta'/\zeta)(c_*+it)\ge\sum_i q_i(t)-B\) for any subset of these pairs and their positive contributions \(q_i\). For \(m\ge1\) and \(B\ge0\), \((\sum_i q_i-B)_+^m\ge\sum_i(q_i-B)_+^m\); hence overlaps and multiplicities introduce no loss. The function \(a[C/a+1.30-B]_+^m\) decreases in \(a>0\) for \(C>0\). Each pair's integral therefore contributes at least
\[
 2a_0\int_0^{2.8}
 \left[\frac1{a_0(1+z^2)}+1.30-B\right]_+^m dz .
\]
Its decreasing integrand is summed by 1024 right rectangles. Independently, (1) at the exact ordinate of any one such zero forces \(-P_A(\gamma)\) greater than .7566, 11.7846 or 28.7636 for \(A=\log T,60,120\), respectively. These are deterministic tests on specified zeta or prime quantities. No upper bounds for the displayed high moments or counts of large signed excursions are assumed.

## A finite prime polynomial which sees one zero

Let \(c=1.4,\lambda=.40,\ A\in\{\log T,45,60,80\}\). The same test (2) holds separately at every one of these four bandwidths. For \(|y|\le.30\) the sole more distant partner satisfies \(K_A(b,y)\ge(b-2/A)/(b^2+y^2)\), which dominates the right side of (2) on a \(40\)-by-\(24\) interval grid. The previous compact rectangle proof covers all other \(y\).

Write \(J_A(t)=\sum_{n\le e^A}\Lambda(n)[n^{-\Theta}(1-\log n/A)-\lambda n^{-c}]\cos(t\log n)\). The omitted subtracted series costs at most \(\lambda e^{-(c-1)v}[v/(c-1)+(c-1)^{-2}]\), using \(\Lambda(n)\le\log n\), \(v=A-10^{-6}\), \(e^v<\lfloor e^A\rfloor\) and a decreasing integral test. Let \(B_A\) denote this tail cost plus \((1-\lambda)\tfrac12\log(T/(2\pi))+.00011\). Set
\[
 q_A(y)=K_A(.01,y)+K_A(.75,y)
             -\lambda[1/(c-\Theta)+1/(c+s-1)]-B_A .
\]
Every right zero in the rectangle forces \(-J_A(\gamma)\ge q_A(0)\). For \(0\le y\le 2/A\) each pair at distance \(y\) has positive-excess-kernel contribution at least \(q_A(y)+B_A\). The superadditivity argument above gives, for \(m\ge1\) and \(R\) zeros in a subinterval \(I\),
\[
 \int_{I+[-2/A,2/A]}[-J_A(t)]_+^m dt
 \ge 2R\int_0^{2/A}[q_A(y)]_+^m\,dy .
\]
The verifier integrates by 256 lower rectangles. If the full rectangle fails, the following are strict lower bounds, with moments normalized by \(T-H+2\).

| \(A\) | threshold for \(-J_A(\gamma)\) at each zero | 12th root of moment | 16th root | 20th root |
|---:|---:|---:|---:|---:|
| \(\log T\) | 5.4067 | .9679 | 1.4751 | 1.9023 |
| 45 | 11.0959 | 1.9577 | 2.9942 | 3.8697 |
| 60 | 16.4348 | 2.8544 | 4.3829 | 5.6776 |
| 80 | 22.8064 | 3.8927 | 6.0034 | 7.7971 |

~~~sh
python -B round7/qrh_strip/strip_positive.py
~~~
