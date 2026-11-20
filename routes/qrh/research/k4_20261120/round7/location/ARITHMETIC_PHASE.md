# The phase at the geometric center of the two fourth powers

Let \(H=3000175332800\) and use the same inputs as the [finite sixth-moment proof](LOCATION_MOMENTS.md). If the fourth-power gap at \(n\) is empty, write \(c_n=2\log(n(n+1))\). In the one finite rectangle
\[
.814<\beta\le7/8,\qquad H<\gamma\le H e^{37/4},
\]
the following three simultaneous count lower bounds hold, with multiplicity:

| Additional requirement on the same zeros | Minimum count |
|---|---:|
| \(\cos(\gamma c_n)>0\) | 596,116 |
| \(\cos(\gamma c_n)>.05\) | 429,638 |
| \(\cos(\gamma c_n)>.10\) | 244,662 |

In particular the phase is specified by the candidate integer. The estimates on the actual phase counts needed to rule out such an integer remain open.

Cover the remaining possible left endpoints by cells \([L,L+1/8]\) beginning at \(115\) and ending past \(147.2\). Define \(M=\exp((L+1/8+10^{-10})/4)\) and \(d=2/M\). Then \(4\log(1+1/n)\le4e^{-L/4}<10^{-10}\) and \(M\ge n+1\). Since \(4\log(1+1/n)\ge4/(n+1)\), the centered tent of radius \(d\) is fully contained in the gap, including zero weights at its endpoints.

By the tent explicit formula at \(c_n\), its positive high-ordinate sum has **real part** at least \(D/2\) when the gap is empty. Remove the two complementary pieces in height and real part by the same validated hinge bounds as in the sixth-moment proof, using this new \(d\). In the remaining finite sum replace \(K_d(\beta-1+i\gamma)\) by \(K_d(i\gamma)=\operatorname{sinc}^2(d\gamma/2)\). The tent integral gives \(|K_d(\beta-1+i\gamma)-K_d(i\gamma)|\le d e^d\) for QRH real parts; multiply by the cumulative undamped weight at a table ordinate strictly higher than \(H e^{37/4}\). The cost is below \(4.46\cdot10^{-11}\). Thus on each cell
\[
\sum_{\rho\ {\rm in\ box}} z_\rho\cos(\gamma c_n)\ge s_L,\qquad
z_\rho=e^{(\beta-1)c_n}\operatorname{sinc}^2(d\gamma/2),\qquad
s_L>0.34068033 .
\]
The computation also bounds \(A_L=\sum z_\rho\) using the all-height hinge table integrated against the squared inverse-frequency envelope. For \(0\le q<1\), the last sum is at most
\[
q A_L+(1-q)e^{-L/8}\#\{\rho\ {\rm in\ box}:\cos(\gamma c_n)>q\}.
\]
The table follows by taking the minimum of the resulting positive lower bound over the physical cells, then rounding up to an integer. It uses all signs in the tent formula and counts only positive ordinates in the rectangle.

~~~sh
python -B round7/location/phase_obstruction.py --width 2 --sub 8 --tight
~~~
