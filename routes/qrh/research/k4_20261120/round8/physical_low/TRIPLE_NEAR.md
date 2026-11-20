# Removing all three-prime moduli from a true multiplier annulus

Take \(q=abc\) with three distinct primes unit to \(Q=23\#\) and \(q>z\). The exact [three-prime sign](TRIPRIME.md) gives \(B_Q(q)\le0\) and
\[
        -B_Q(q)\le2(L_aL_{bc}+L_bL_{ac}+L_cL_{ab}),
        \qquad L_d=|\lambda_d|.
\]
In particular the actual multiple term in the full Poisson sum contributes nonpositively even on its nearest integer resonance. With \(v=X/q\ge w=e^c/q\), the normalized four-sided finite band from [the physical calculation](PRIME_GAP_BLOCK.md) therefore obeys
\[
 P_q\le \frac{|B_Q(q)|}{q}
 \left[M^+\{\eta+18M(\lfloor 2Q/v\rfloor)/Q\}+U(v)\right],
 \quad M^+=u_0\{e^{2r}A+2(.0002)e^{116-c}S_0\}.
\]
The positive \(U(v)\) is the per-modulus high-harmonic bound used there. This directly covers every integer multiplier including ones divisible by \(a,b\) or \(c\), and all boundary frequencies in \(2<hX/(Qq)\le2.5\cdot10^{17}\).

For the term where \(a\) is singled out, order \(b\le c\); summing over all singletons and ordered pairs \(b\le c\) covers exactly the three displayed products, besides harmless positive repetitions if primes coincide. Fix a slab \(w_0\le w\le w_1\), and put \(p_0=e^c/(w_{\mathrm{end}}z)>1\). The true conditions \(a,bc\le z\) imply \(a\ge p_0,\ c\ge\sqrt{p_0},\ b\le\sqrt z\). In outer bins \(a_l\le a\le a_h,\ b_l\le b\le b_h\), the third prime satisfies
\[
 L=\max(\sqrt{p_0},b_l,e^c/(w_1a_h b_h)), \qquad
 U=\min(z/b_l,e^c/(w_0a_l b_l)).
\]
For every *fixed* first two primes, its clipped interval inside \([L,U]\) has log length at most \(\min(\log(U/L),\log(w_1/w_0))\). The second length is essential for keeping the cost of the complete annulus small when the outer bins are wide. Its \(1/c\) harmonic is at most this minimum plus \(2E(U)/L\), all divided by \(\log L\), plus \(1/L\) for a closed endpoint; use Johnston (3.2) as in the preceding estimate. Multiply by \(L/(L-1)\) to obtain the needed upper on \(1/(c-1)\).

The outer \(a\)-harmonic and all \(b\) bins beyond the finite sieve use the same prime bound. For \(b\) in bins ending below \(10^5\), charge every actual prime in the outward-rounded integer interval, at weight \(1/(b-1)\). The two Selberg numerators are at most \(G_Q(z/a_l)G_Q(zw_1a_h/e^c)\) besides \(\rho(a)\rho(b)\rho(c)/G_-^2\). Multiply the summed positive terms by twice the bracket above taken at \(w_0\). The tested entire three-prime finite-band contributions satisfy:

| \(2500\le e^c/q\le w_{\rm end}\) | Upper |
|---:|---:|
|3500|.001338033|
|11000|.005461389|
|30000|.009922136|
|100000|.016082116|

As one combined example use the complete wheel at \(m=1700,Y=e^{75}\), whose allowance before the high charge exceeds \(-.033457024585\). Add [.04414230 of true negative four-sided modulus contributions](FOUR_GAP_BLOCK.md), subtract the entire common high tail .000067041579, and pay every complementary semiprime through \(w=11000\) at .003100120. Paying the complete three-prime cost .005461389 then leaves a sufficient allowance **.00205672**. Thus all \(q>X/1700\), all \(q\le e^{75}\), the whole negative class \({\cal S}\), and every \(q\) of at most three prime factors in \(2500\le e^c/q\le11000\) are removed from that signed remainder. In this whole annulus a nonzero contributing modulus still in the task must have at least four distinct prime factors. The remaining signed inequality and the point \(L=116\) are open.

~~~powershell
python -B round8/physical_low/triple_near.py --end 11000 --upper .005461389
python -B round8/physical_low/triple_near.py --end 30000 --upper .009922136
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 1700 --harmonic-limit 446185740 --tiny-log 75 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower=-.033457024585
~~~

2026-11-20. Joint project attribution to Claude and Codex.
