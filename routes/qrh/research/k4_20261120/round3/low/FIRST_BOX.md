# Height bands in the first zero rectangle

Assume the [finite-rectangle theorem's analytic inputs](../../round2/spectrum/FINITE_BOX.md).
If a fourth-power interval with \(114.992\le L=4\log n\le123\) has no
prime, its first rectangle must now contain at least **51,327** zeros
of positive height, counted with multiplicities:
\[
    .8<\beta\le7/8,\qquad 3\cdot10^{12}<\gamma\le e^{37}.
\]
Previously the threshold was 40,001. In conjunction with the other
three rows of the finite-rectangle theorem, any fourth-power
counterexample requires at least 51,327 such zeros up to \(e^{57.6}\).
These are necessary conditions on a counterexample. The counts of
off-critical-line zeros at these heights are unknown.

More precisely, retain the original weight
\[
 v(\rho)=e^{-(7/8-\beta)114.992}
       \min(1,4/[ab\,d(123)^2\gamma^2]),\quad
 a=1/4,\ b=3/4,\ d(L)=\log(1+4e^{-L/4}).
\]
Let \(W_j\) be its sum over the four respective positive-ordinate
intervals \((H,e^{30}],(e^{30},e^{31}],(e^{31},e^{33}],(e^{33},e^{37}]\),
with \(H=3\cdot10^{12}\). A counterexample in this first \(L\) band
requires
\[
    \frac{W_1}{51\,326}+\frac{W_2}{183\,930}+
    \frac{W_3}{611\,919}+\frac{W_4}{611\,919}>1.                    \tag{1}
\]
Keeping only the smallest denominator gives the unweighted integer
condition. The two highest bands have the same rounded threshold
because for both, the last \(L\) cell limits the bound relative to
this fixed weight.

Take \([l,r]\) to be a cell of the previous first-row proof. For a
zero with \(\gamma\ge h\) in this cell, consider a single uniform factor
of the Mellin transform with width \(w=a\) or \(b\). Removing damping
costs at most \(wd(l)/2\), by
\(1-e^{-(1-\beta)d(L)t}\le d(l)t\). With \(u=w h d(r)/2\), bound the
remaining modulus for any \(\gamma\ge h\) by
\[
 S(u)=
 \begin{cases}
 \max(\sin u/u,1/\pi),&0<u<\pi,\\
 1/u,&u\ge\pi .
 \end{cases}
\]
Indeed \(\sin u/u\) decreases on \([0,\pi]\); after \(\pi\) one uses the
reciprocal of the argument. Thus the product of the two factors in
this cell is at most
\[
 M(h)=\prod_{w=a,b}\min(1,S(w h d(r)/2)+w d(l)/2).
\]
It is independently at most \(4/[ab\,d(r)^2\gamma^2]\) by the
antiderivative of the damped exponential. If \(\lambda\ge0,\ 0\le M\le1\),
then \(\min(M,\lambda u)\le\max(M,\lambda)\min(1,u)\) for \(u\ge0\).
Consequently for positive and negative ordinates together in band \(j\)
the normalized cost is bounded by \(2e^{-l/8} q_{ij} W_j\), where
\[
 q_{ij}=\max\!\left(M(h_j),\,d(123)^2/d(r)^2\right),\qquad
 h_j=H,\ e^{30},\ e^{31},\ e^{33}.
\]
The real-part discount in \(v\) applies since \(L\ge114.992\).

Write \(P_i\) for the prior certified total cost in this cell of
zeros with \(\beta\le.8\), the tail above \(e^{37}\), prime powers,
and the trivial zeros. We use exactly the old parameters, upper
endpoint tail and its \(0.14\) decay transfer. Define
\(A_i=(1-P_i)e^{l/8}/2\). The [160-bit Arb verifier](first_box.py)
checks every \(A_i>0\) and each \(A_i/q_{ij}>C_j\), where \(C_j\)
is the denominator in (1). If its left side is at most 1, the
finite-rectangle cost plus \(P_i\) is strictly less than 1 for every
real \(L\) in the row. This forces a prime in the target open interval.

The finite minima found for the four bands exceed \(51326.81\),
\(183930.60\), \(611919.54\), and \(611919.54\). The first is limited
by \(116.25\le L\le116.5\), the second by \(116.75\le L\le117\).
Reproduce with \(\texttt{python -B first_box.py}\). The count statement
follows from the written analytic bounds and numerical certificate;
it has no independent Lean formalization. Project attribution to
Claude and Codex. Codex derived the four height discounts.
