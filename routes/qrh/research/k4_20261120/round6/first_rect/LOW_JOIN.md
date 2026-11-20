# Continuous lower-end extension under QRH(7/8)

Write \(L=\log(n^4)\), \(H=3000175332800\). The [fifth-round certificate](../../round5/low/NARROW_COVER.md) reaches the closed endpoint \(115.036065\). This note joins a locally frozen dual AFE to that certificate, keeping its explicit [squarefree Farey addition](../../round5/low/SQUAREFREE_FAREY.md) \(1.16613\). The same trigonometric Fourier kernel, separate physical prime tail, cumulant counting bound, and half-axis symmetry as in the earlier certificate are used.

| Closed \(L\) interval | Upper bound on complete normalized cost | Calculation |
|---|---:|---|
| \([115.036065,115.038000]\) | \(0.9995860\) | 24 height cells |
| \([115.038000,115.040500]\) | \(0.999984507204\) | 40-cell spectral reference and physical reevaluation |

For the first row take \(K-H=8000000000\). For the second take \(K-H=14000000000\). Put \(S=K-H,\ Q=10000\), and partition \([0,S+128Q]\) at the points
\[
 d_i=(S+128Q)z(1+3z)/4,\qquad z=i/M.
\]
At its rounded-up right endpoint \(D_i=\lceil d_i\rceil\), bound the true positive-ordinate weighted sum
\(\sum_{H<\gamma\le H+D_i}e^{(\beta-1)l}\) by the piecewise-linear real-part majorant of \(e^{(\beta-1)l}\). Each hinge integral uses the local fourth moment of \(\zeta E_6\) from the [translated projected AFE proof](PROOF.md), the projected short-filter joint second and signed first moments there, and the two-edge Jensen bound from the previous round. The [verifier](low_replay.py) uses \(q=6,\alpha=1.25,p=1\), one time cell per height endpoint, flat-taper parameters \((\delta,W,\log h)=(.68,8,-3)\), and short cores \(512,2048,8192\). It includes the finite RH count and all fixed side errors.

For \([l,h]\) set \(a=(1-10^{-12})K\log(1+4e^{-h/4})/2\). The cap at the left of one height cell is
\[
 c_i=\frac{\min(1,\sin(\min(\pi/2,[a(1-(H+d_i)/K)]_+))+2Qa/(\sqrt\pi K))}{\sin a}.
\]
In the last difference set \(c_M=0\). The finite high-zero charge is at most
\[
 2e^{1/(16Q^2)}\sum_{i=1}^M(c_{i-1}-c_i)
       \sum_{H<\gamma\le H+D_i}e^{(\beta-1)l}.
\]
Replacing the positive inner sum by its certified upper bound is valid because the cap differences are nonnegative. Replacing each cell's right edge by its integer ceiling enlarges its inner set, even if a zero lies on that edge. The Gaussian tail beyond \(K+128Q\) is below \(10^{-1700}\) and is reevaluated with each new \(a\).

The 40-cell reference rectangle uses \(l_0=115.038000,\ h_0=115.040000\). Only its finite high-zero charge, rounded up to \(0.005055995921\), is used on the second row. Since \(l\ge l_0\), all zero weights decrease. If \(h<h_0\), put \(r=a(h)/a(h_0)\). The sinc decrease on \([0,\pi/2]\) shows that the entire new spectral step function is at most \(r\sin(a(h_0))/\sin(a(h))\) times its reference value. If \(h\ge h_0\), the factor is one because \(a\in(\pi/2,\pi)\) decreases. This compares the cap pointwise before integration and requires no comparison of successive differences. The [short transfer](low_join.py) recomputes the arithmetic and verified-zero contributions at the actual target slab endpoints.

Run from the directory containing the round folders, at 192-bit Arb precision as set in the scripts.

~~~powershell
python -B round6/first_rect/low_replay.py --lo 115.036065 --hi 115.038000 --size 8000000000 --panels 24 --mesh 1/4 --case .68,8,-3 --check
python -B round6/first_rect/low_replay.py --lo 115.038000 --hi 115.040000 --size 14000000000 --panels 40 --mesh 1/4 --case .68,8,-3 --check --check-high .005055995921
python -B round6/first_rect/low_join.py --lo 115.038000 --hi 115.040500 --check
~~~

The shared endpoint \(115.038000\) is included twice. Hence the preceding closed range continues through \(L=115.040500\). The intervening range up to the separately proved far end still requires additional information about zeros. The proof is handwritten with numerical enclosures.

The 40-cell reference itself has full cost below \(0.999783403380\). The last integer at the certified endpoint is \(\lfloor e^{115.040500/4}\rfloor=3092883675597\).
