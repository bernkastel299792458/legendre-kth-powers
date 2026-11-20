# Four distinct primes in the negative finite-band class

Use exactly the wheel \(23\#\), location \(L=116\), spatial criterion \({\cal S}\), hard Fourier band and normalization in [the physical phase estimate](PRIME_GAP_BLOCK.md). In addition to its two-prime contribution \(<-.02330281\), the four-prime moduli in \({\cal S}\) contribute
\[
  \sum_{\substack{q\in{\cal S}\\\omega(q)=4}}P_q<-.02083949.
\]
Other members of \({\cal S}\) are nonpositive. Together the two disjoint families give \(\sum_{q\in{\cal S}}P_q<-.04414230\). Every frequency of every such modulus is included within the stated finite band. Here both selected subfamilies have \(q>e^c/10^{10}>e^{92}\).

## An exact positive coefficient evaluated at its true cutoffs

For distinct primes \(a,b,P,R\) set \(q=abPR\). Take \(a,b\) to be the two smallest primes and suppose
\[
 PR>z,\qquad A=z/(aP)<b,\qquad B=z/(bR)<a,\qquad A,B\ge1.
\]
Write \(L_d=|\lambda_d|\), including \(L_d=0\) for \(d>z\). Each of the two large primes must be assigned to a different divisor. Further, \(abP>z,abR>z\); thus neither divisor may contain *both* small primes. To generate the full lcm each divisor consequently contains exactly one small prime. The whole coefficient is
\[
           B_Q(abPR)=2(L_{aP}L_{bR}+L_{bP}L_{aR}).
\]
This identity includes the case where the second product is zero. For a squarefree \(d\) unit to \(Q\), \(L_d=\rho(d)G_{Qd}(z/d)/G_Q(z)\). One always has \(G_Q(t)\le\rho(d)G_{Qd}(t)\) since separating primes of \(d\) from the squarefree divisor in the numerator costs at most \(\prod_{p\mid d}(1+1/(p-1))=\rho(d)\). Thus \(L_{aP}L_{bR}\ge G_Q(A)G_Q(B)/G_Q(z)^2\), even when a small prime is below a row cutoff.

Count these two products by ordered \((a,b)\) and ordered \((P,R)\). For each actual modulus there are at most two orderings producing each cross product. The preceding coefficient pays exactly those two copies, even when the selected ratio ranges count only some of its assignments. Every retained modulus is in \({\cal S}\) with \(B_Q>0\); hence the lost assignments and all other moduli of the same sign only lower the full signed sum.

## Measuring the selected assignments

The two small primes are placed in the disjoint intervals with boundaries
\[
 100,300,1000,3000,10000,30000,100000,300000,10^6,10^7,10^8,10^9,10^{10},3\cdot10^{10}.
\]
For distinct bins \(I=(a_l,a_h],J=(b_l,b_h]\), \(a_h\le b_l\), the total harmonic mass of the two small-prime orderings is \(2H(I)H(J)\). In a single bin it is at least \(H(I)^2-1/a_l\), by removing the diagonal. Here \(H\) is a lower bound on prime reciprocal mass. Sum primes through \(10^5\) in Arb, and beyond apply the Johnston harmonic bound of the preceding proof on successive intervals of ratio at most two.

For each fixed small ordered pair partition the *effective* divisors \(aP,bR\) into the same kind of logarithmic bins as in the two-prime proof. The ratios \(A<B_{\rm small}=b_l,\ B<a_l\) are ensured by their separate bin cutoffs. The code requires \(P,R>b_h\) on the whole cell and \(PR>z\) after allowing the largest products \(a_hb_h\) of the two small bins. The set of small primes in a retained modulus is therefore unique. With distinct small bins all ordered effective rectangles are evaluated. If the small bins coincide, symmetry permits one triangle with each off-diagonal counted twice.

In an effective interval \((l,h]\) whose actual prime denominator is a varying \(d\in[d_l,d_h]\), the prime harmonic lower is
\[
 \frac{\log(h/l)-2d_h E(h/d_h)/l}{\log(h/d_l)}.
\]
Indeed \(dE(h/d)\) increases in this range, since its logarithmic derivative is \(1/2-1/\log(h/d)-1/(\log(h/d)-2)>0\) for the verified \(\log(h/d)>6\). In the excluded actual prime intervals the shortest ordinary length used in Brun–Titchmarsh is divided by \(d_h\). The lower prime endpoint and the harmonic charge for a possible boundary or repeated \(P=R\) are scaled by the matching row's divisor bound. If the lower length is at most ten, only the clipped \(\vartheta\) estimate is used. The number of candidate unit multipliers still uses the *effective* variables unchanged, because \(w=e^c/[(aP)(bR)]\). This proves the uniformly counted lower mass for each fixed \(a,b\); the extra factor \(1/(ab)\) in \(B_Q(q)/q\) is accounted for by the small-prime harmonic sums above.

The executable prices 91 small-bin pairs and 415736 accepted effective prime rectangles. Its rigorous lower endpoint exceeds .02083949. The upper and lower budgets in the next paragraph concern a single prescribed point and are independent of the arrangement of the four prime factors in the true integer multiples.

## Two simultaneous cuts on the complete remainder

* With \(m=2500,Y=e^{75}\), all \(q>X/2500\) are paid, including every \(\Omega(q)\) and every unit integer multiplier. The original wheel allowance before the tightened upper tail exceeds \(-.0429023711400\). After charging the absolute tail .000067041579, adding the disjoint negative margin .04414230, and paying all complementary semiprimes at \(2500\le e^c/q\le3500\) for .000596132, it suffices that the remaining signed sum be **below .00057675**.
* With \(m=1000,Y=e^{77}\), the full wheel allowance before the tightened upper tail exceeds \(-.039714873677\). The analogous true signed sum after paying all complementary semiprimes through \(e^c/q=11000\) for .003100120 need only be **below .00126026**.

Both remaining sums run over \(Y<q\le X/m,\ 2<hX/(Qq)\le2.5\cdot10^{17}\), excluding \({\cal S}\) and the stated semiprimes. Every member of \({\cal S}\) is present at either choice of cutoffs. The sufficient allowances do not establish either remaining inequality.

~~~powershell
python -B round8/physical_low/four_gap_block.py --grid 90 --asymmetric --lower .02083949
python -B round8/physical_low/prime_gap_block.py --top 10000000000 --grid 640 --spatial-tail --refined --lower .02330281
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 2500 --harmonic-limit 446185740 --tiny-log 75 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower=-.0429023711400
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 1000 --harmonic-limit 446185740 --tiny-log 77 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower=-.039714873677
python -B round8/physical_low/prime_near_block.py --end 3500 --upper .000596132
python -B round8/physical_low/prime_near_block.py --end 11000 --upper .003100120
python -B round8/physical_low/spectral_tail.py --Q 223092870 --cut 200 --kappa 2.5e17 --upper .000067041579
~~~

2026-11-20. Joint project attribution to Claude and Codex.
