# Testing a recent local zero-density formula on the first selected box

The [rStation manuscript, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/168) gives an explicit local count using exact Selberg coefficients and both branches of a moving approximate functional equation. Its parameterized theorem allows the height here. The numerical expression in that theorem, even summed over arbitrary subdivisions of \(H<\gamma\le2H\), exceeds \(1\,082\,428\,176\) for \(\sigma=.854\). The target for the larger [first selected box](SELECTED.md) is \(805\,224\).

Here \(H=3000175332800\). On a subinterval starting at \(T\in[H,2H]\) of length \(\Delta\), write \(a=2\sigma'-1\), \(h=\sigma-\sigma'=(.708-a)/2\), \(u=\log X\). Then \(0<a<.708,\ \log 8\le u\le\log(2H/(2\pi))\). The formula contains the positive terms \(A_\Delta,R_\Delta\) in its upper bound for \(V_\Delta\). Since \(\zeta(1+a)\le1+1/a\), \(X\le x\) and \(T\le2H\), these terms satisfy
\[
A_\Delta\ge e^{-au}/(1+a),\qquad
R_\Delta\ge \pi(15.203)^2(1+u)^2 e^{(1-a)u}/H .
\]
The numerical count formula is at least \(\Delta\log(1+(\sqrt{A_\Delta}+\sqrt{R_\Delta})^2)/(2\pi h)\). Lower-bound its coefficient of \(\Delta\) throughout the rectangle using 200 by 160 cells. For \(A_\Delta\) substitute the upper values of both variables. For \(R_\Delta\) substitute the upper \(a\) and lower \(u\). Use the lower \(a\) to upper-bound \(h\). Summing \(\Delta\) gives \(H\) on every partition. This is a limitation of the displayed numerical bound, with its particular AFE remainder and main diagonal. It gives no lower bound for the number of actual zeta zeros. The newer [localized theorem of Ye](https://arxiv.org/abs/2610.15989) states a density bound on real parts from .7 to .8 and includes an unspecified implied constant. Neither formula furnishes the missing count at .854.

~~~sh
python -B round7/first_selected/centered_comparison.py
~~~
