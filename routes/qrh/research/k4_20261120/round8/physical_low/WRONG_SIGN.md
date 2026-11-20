# Paying every exception to the alternating Selberg sign

For squarefree \(q\) put \(E(q)=\max(0,-\mu(q) B_z(q))\). At \(L=116\) in the [physical middle condition](REMAINING_PHASE.md), on the **whole** annulus \(X/50<q\le X/23\), the normalized contribution of \(E(q)\) to the actual multiple count is below \(9.043441\,10^{-8}\). Its contribution to the main-plus-low correction is below \(2.098144\,10^{-7}\). No restriction on the number or sizes of the prime factors remains in these two totals. Thus discarding all coefficients of incorrect sign costs less than \(3.002491\,10^{-7}\) in absolute value in the signed middle (including the uniform \(2.03\,10^{-13}\) high-frequency tail). Replacing those coefficients by their negatives doubles the cost. The main contributions of the correctly signed moduli still require estimates.

| Lower open endpoint | Wrong-sign physical upper | Wrong-sign main plus low upper |
|---|---:|---:|
|\(X/30\)|\(1.846005\,10^{-9}\)|\(4.517203\,10^{-9}\)|
|\(X/36\)|\(5.300541\,10^{-9}\)|\(2.494717\,10^{-8}\)|
|\(X/40\)|\(1.588806\,10^{-8}\)|\(5.334985\,10^{-8}\)|
|\(X/50\)|\(9.043441\,10^{-8}\)|\(2.098144\,10^{-7}\)|

## A finite formula for the true coefficients

Let \(R=z^2/q\), and \(S=\prod_{p\mid q,\ p\le R}p\). As in [the Boolean sign lemma](BOOLEAN_SIGN.md), disjointly partition \(q/S=D E\) among the two outer rows. For a permitted \(i\mid S\), its row, before dividing by \(G_Q(z)\), is
\[
 \rho(Di)G_{QDi}(z/(Di))
 =\rho(D)\sum_{\substack{k\le z/D\\(k,QDS)=1}}\frac{\mu^2(k)}{\varphi(k)}
     L_i(z/(Dk)),\quad
 L_i(y)= i\sum_{\substack{v\mid S,\ i\mid v\\v\le y}}1/\varphi(v).
\]
This follows by splitting the extended squarefree divisor in \(i\sum_{i\mid t\le z/D}1/\varphi(t)\) into its part supported on the primes of \(S\) and its part coprime to them. Both are coprime to \(QD\). For two such rows, the contribution normalized by \(\mu(q)\) has finite inner value
\[
 (-1)^{\omega(S)}\sum_{[i,j]=S}\mu(i)\mu(j)L_i(y)L_j(v)
 =\rho(S)\sum_{\substack{a,b\mid S,\ [a,b]=S\\a\le y,\ b\le v}}
       \prod_{p\mid(a,b)}-\frac{p-2}{p-1}.
\]
At a prime occurring on just one side the local sum over \(i,j\) before the outer sign is \(-p\), and when it occurs on both sides this sum is \(p^2-2p\). Dividing by \(\varphi(a)\varphi(b)\) gives the formula. Here \(y=z/(Dk),v=z/(El)\), so for every inner pair, \(kl(a,b)\le R\). In the verified ranges \(R<121\). A negative summand needs at least one shared prime \(\ge11\), while every nonunit \(k,l\) coprime to \(210\) is \(\ge11\). Therefore **all terms with \(kl>1\) are nonnegative**. For the negative part, it suffices to retain \(k=l=1\), take the negative part of that inner block, and then sum over outer partitions. The Boolean sign lemma allows omission of \(\omega(S)\le3\), even before this simplification.

Let \(m=S,\ h=\varphi(S)\). For fixed \(S\) sort its divisors, and on the grid of their successive thresholds in \(y=z/D,\ v=z/E\) form the integer cumulative sum \(C\). At \((a,b)\) with \([a,b]=S\) add \(h\) for \((a,b)=1\), or subtract \(h(p-2)/(p-1)\) for \((a,b)=p\). Products \(ab>mR_{\max}\) can never contribute. Gcd values with two shared primes cannot occur for \(R_{\max}<121\). The sign-corrected inner row equals \(\rho(S)C/h\). Only cells with \(C<0\) need paying. The program enumerates every subset \(S\) of the unit primes \(\le z^2\,\mathrm{end}/X\). The actual range of \(z/D,z/E\) in the final unbounded grid cells is capped by \(yv\le mR_{\max}\). Since the outer sum is over ordered \(D,E\), off-diagonal cells have multiplicity two.

## Bounding the two outer rows

Every \(D,E\) is coprime to \(B=\mathrm{rad}(Q S\prod_{p\le z^2\,23/X}p)\). Put \(\eta_B=\varphi(B)/B,\ \tau_B=2^{\omega(B)}\), and \(Z_B=\prod_{p\nmid B}(1+1/[p(p-1)])\). The upper product tail after the integer \(\mathrm{end}\) is at most \(\exp(1/\mathrm{end})\). For a closed interval \(1<L\le U\) its \(\rho(n)/n\)-weighted, \(B\)-coprime harmonic sum is at most
\[
 \mathcal H(L,U)= Z_B\{\eta_B\log(U/L)+(2\tau_B+1)(1+\log U)/L\}.
\]
Indeed \(\rho(n)=\sum_{j\mid n}\mu^2(j)/\varphi(j)\). After writing \(n=j k\), the unweighted coprime harmonic sum in \(k\) is bounded by \(\eta_B\log(U/L)+(2\tau_B+1)j/L\) by divisor inversion, or by integrating the bounded counting discrepancy. Summing the error uses \(\sum_{j\le U,(j,B)=1}1/\varphi(j)\le Z_B(1+\log U)\) by the same expansion. The corresponding \(\rho(n)\) ordinary count in any interval of length \(v\) with upper end at most \(U\), after intersection with the projected cell, is at most \(Z_B[\eta_B v+(\tau_B+1)(1+\log U)]\). This follows directly from inclusion-exclusion in each \(k\)-interval, with its two endpoints handled by unit divisor errors.

In a grid cell project both factors to their intersections with \(X/(m\,\mathrm{end})< DE\le X/(m\,23)\), obtaining \([D_l,D_h],[E_l,E_h]\). To price the inverse mean plus low contribution, use the maximum of the true
\[
 \eta+\frac2Q\sum_{1\le n\le QmDE/X}c_Q(n)\cos(2\pi nt/(QmDE))
\]
over that rectangle and \(X_-\le t\le X\), admitting zero whenever a frequency can be absent. The joint multiplier is positive throughout the true region. Multiply this upper by \(|C|\mathcal H(D_l,D_h)\mathcal H(E_l,E_h)/h^2\) and by the physical normalizer \(P_0\,\mathrm{mass}/G_Q(z)^2\), where \(\mathrm{mass}=XA/H+2\delta S_0\). The denominator \(h^2\) comes from \(\rho(S)/(hS)=1/h^2\). Exact cutoffs depend on \(q\); the projected positive sum safely includes excess tuples.

For genuine physical multiples \(kq\) only \(23\le k<\mathrm{end},(k,210)=1\) occur. Trim the outer \(D\)-range further using \(X_-<k m D E<X\). For a given outer \(D\), use the ordinary count above separately on the superlevel intervals of the physical leakage, after its dilation and its probability translation. The cumulative length contributes \(\eta_B Z_B\,\mathrm{mass}/(k m D)\). The summed peak heights are at most \(S_0\), giving the additive error \(Z_B(\tau_B+1)(1+\log E_h)S_0\). Each interval is clipped to \(E\le E_h\) before applying this bound. Multiply through by the true row weights and sum over outer \(D\), bounding the unweighted outer \(\sum\rho(D)\) by \(D_h\mathcal H(D_l,D_h)\). After the \(m\) from \(\rho(S)/h=m/h^2\) is included, the resulting bound for each \(k\) is
\[
 \frac{P_0}{G_Q(z)^2}\frac{|C|}{h^2}\,
 Z_B\mathcal H(D_l,D_h)
 \{\eta_B\,\mathrm{mass}/k + m(\tau_B+1)(1+\log E_h)S_0D_h\}.
\]
All true Selberg coefficients, including squarefree, coprimality and reciprocity restrictions, are accounted for before these positive enlargements.

~~~powershell
python -B round8/physical_low/exact_wrong_sign.py --end 50 --upper .0000002098144
python -B round8/physical_low/exact_wrong_sign.py --end 50 --physical --upper .00000009043441
~~~

A simpler four-dimensional estimate remains available up to \(X/200\). Of the 22 ordered negative pairs in the Boolean table, one family consists of every proper subset, while its partner contains at least five of the six pair subsets. The absolute negative integer is at most two. For \(S=abcd,\ a<b<c<d\) this requires \(y=z/D\ge bcd,\ v=z/E\ge bd\) up to interchanging the rows; thus \(R\ge bd/a\), \(y\le acR\), \(v\le aR\). The normalized heights of the two implicated levels are bounded respectively by \(\rho(bcd)G_Q(y/(bcd))\) and \(\rho(bd)G_Q(v/(bd))\): among the last row's two largest pair divisors \(bd,cd\) at least one is present, with \(\rho(cd)\le\rho(bd)\). Together with the two orientations this costs at most four times their product, after extracting \(\rho(D)\rho(E)\). Partition the first row logarithmically and apply the previous harmonic row bounds. At \(X/200\) the program prices 20,414 possible four-prime sets and gives the upper .0000184482 on the harmonic exception with exactly four small primes. Additional dimensions are not included at that larger endpoint.

~~~powershell
python -B round8/physical_low/sign_exception.py --end 200 --cells 12 --upper .0000184482
~~~

## A symmetric polynomial bound in higher dimensions

For \(R<121\) every negative summand of the finite formula has a single common prime \(p\). Dropping all favorable disjoint terms prices any dimension \(s\) by summing those singleton-overlap contributions. Write the two divisor indices as \(pA,pB\), where \(AB=S/p,\ (A,B)=1\). Each assignment of the other \(s-1\) primes to the two sides is allowed. Its harmonic coefficient before the row sums is
\[
 \frac{p-2}{(p-1)^2}\prod_{\ell\mid S/p}\frac1{\ell-1}.
\]
By symmetry orient each pair so \(A\ge B\), retaining its original multiplicity. Put \(R_0=z^2\,\mathrm{end}/X\). Each outer integer lies in a multiplicative interval of log span \(h=\log(R_0/p)\), with lower bounds \(D\ge z/(R_0 A)\), \(E\ge z/(R_0 B)\) and \(D\le z/(pA)\). For a selected \(p\) let \(P_j\) be the product of the \(j=s-1\) largest other admissible primes. This gives uniform lower endpoints \(z/(R_0 P_j)\) and \(z/(R_0\sqrt{P_j})\) for the two respective harmonic bounds. For a lower bound \(l\) on a lower endpoint, use \(l'=\max(1,l)\). The arithmetic error divided by that endpoint is bounded by \((1+h+\log l')/l'\), a decreasing function on \(l'\ge1\). This includes cells with fractional lower endpoint by restricting to positive integers.

For the leading harmonic and physical terms sum the assignments by taking the coefficient of \(t^j\) in \(\prod_{\ell\ne p}(1+2t/(\ell-1))\), using the appropriate uniform bounds above. For the physical counting remainder one has \(SD_h\le z\sqrt{S/p}\); use instead the coefficient of \(t^j\) in \(\prod_{\ell\ne p}(1+2\sqrt{\ell}\,t/(\ell-1))\). Also \(E_h\le z\). The physical term uses the same \(k\) range; the leading factor sums \(1/k\) and the additive remainder sums one per \(k\). In either harmonic row one may use the best of the three moduli \(1,210,\prod_{p\le19}p\). The physical ordinary estimate takes the best *combined* slope-plus-remainder across these moduli. These formulas price arbitrary residual outer factors and all remaining dimensions without explicit enumeration of their full Boolean lattices.

At \(\mathrm{end}=100\), dimensions at least 6 cost less than .000049823 harmonically and .000026890 physically. Adding both exact dimensions 4 and 5 (respectively .000003183356 and .000001281576 for the two costs) allows the alternating sign on this larger annulus with clipping cost less than **.00008118**, including the high tail. Every eligible \(23\le k<121\) is prime. If \(\lambda_{\rm L}\) denotes the Liouville function, then for a contributing squarefree \(q=n/k\) one has \(\mu(q)=-\lambda_{\rm L}(n)\). For a fixed genuine physical multiple \(n\), all the clipped terms across this range of \(k\) have the same sign.

~~~powershell
python -B round8/physical_low/rare_sign.py --end 100 --threshold 6
python -B round8/physical_low/exact_wrong_sign.py --end 100 --maxdim 5 --upper .000003183356
python -B round8/physical_low/exact_wrong_sign.py --end 100 --maxdim 5 --physical --upper .000001281576
~~~

The exact six-dimensional sum gives a sharper \(m=100\) result. Harmonic and physical bounds through dimension 6 are .000003354508 and .000001531731; the respective bounds for all dimensions \(s\ge7\) are .000006194844 and .000003491056. Thus the entire clipping error at \(X/100\) is **less than .000014573**, with the high tail included.

~~~powershell
python -B round8/physical_low/exact_wrong_sign.py --end 100 --maxdim 6 --upper .000003354508
python -B round8/physical_low/exact_wrong_sign.py --end 100 --maxdim 6 --physical --upper .000001531731
python -B round8/physical_low/rare_sign.py --end 100 --threshold 7
~~~

The same programs allow \(R<209\). For a nonunit \(kl\ge11\), put \(w=yv/S\le R/(kl)<19\). Each nonzero summand in the two-row \(L_i(y)L_j(v)\) has \((i,j)\le w\), since \(i\le y,\ j\le v,\ [i,j]=S\). Partition every prime \(>w\) disjointly between \(i\) and \(j\). The remaining at most three primes are among \(11,13,17\). The finite rows \(L_i(y)\) themselves decrease under adding divisors: equivalently \(L_i(y)=\rho(i)\sum_{n\mid S/i,\ n\le y/i}1/\varphi(n)\), and the same divisor split as for \(A_i\) proves monotonicity. The Boolean sign lemma on the remaining coordinates gives the correct sign for every \(kl>1\) block. In the \(k=l=1\) exact table a double overlap contributes \(+h\prod_{p\mid(a,b)}(p-2)/(p-1)\); no triple overlap can occur in this range. This positive contribution may be omitted in the higher-dimensional estimate.

For the *actual multiple count* on the entire larger prefix \(q>X/100\), there is a one-variable signed form. Put \(W(n)=\sum |B_z(n/k)|\), summing over prime divisors \(k\) of \(n\) from 11 through 97 such that \(q=n/k>X/100\), coprime to \(Q\), and include only integers \(n\) coprime to \(Q\). Then
\[
 \left|P_0\sum_{\substack{q>X/100\\(q,Q)=1}} B_z(q)
   \sum_{(k,Q)=1}F(kq)
 +P_0\sum_{(n,Q)=1}\lambda_{\rm L}(n)F(n)W(n)\right|<.000010046 .
\]
For \(q>X/23\) the only nonzero actual multipliers are \(11,13,17,19\): multiplier 1 has no support because \(z^2<X_-\), and the next one, 23, is too large. Each such multiple has \(z^2/q=k z^2/(kq)< k<247/11\), so its corresponding Selberg sign is exact by [the sharp onset](BOOLEAN_SIGN.md). For \(X/100<q\le X/23\), each \(k\) is also prime, with the first six and all higher dimensions together giving physical wrong-sign cost below \((1.531731+3.491056)10^{-6}\). Changing that sign costs twice the latter amount. For squarefree \(q\), \(\lambda_{\rm L}(kq)=-\mu(q)\) even when \(k\mid q\); nonsquarefree \(q\) have zero coefficient. This reduces all actual frequencies on the prefix to one weighted Liouville sum while leaving the prime-interval inequality open.

At endpoint 200, summing dimensions 4 and 5 by the exact table gives .000020143003 harmonically and .000012442738 physically. Summing every \(s\ge6\) by the symmetric polynomials gives .000476463130 and .000321143144. Thus on the entire \(X/200<q\le X/23\) annulus clipping the exceptional signs costs less than **.000830193** including the high tail. In this longer annulus the admissible multipliers include composite integers; a one-variable expression uses their own factor \(\lambda_{\rm L}(k)\) in front of each inner weight.

~~~powershell
python -B round8/physical_low/exact_wrong_sign.py --end 200 --maxdim 5 --upper .000020143003
python -B round8/physical_low/exact_wrong_sign.py --end 200 --maxdim 5 --physical --upper .000012442738
python -B round8/physical_low/rare_sign.py --end 200 --threshold 6 --upper .000476463130 .000321143144
~~~

## Absorbing the first small primes into the exact calculation

At the \(X/23\) boundary, choose \(t\ge4\), and for every higher-dimensional \(S\) let \(T\) consist of its first \(t\) primes in increasing order. All blocks with no overlapping prime in \(S/T\) are already paid by the dimension-\(t\) exact estimator. To see this, partition \(S/T=A B\) according to the two sides and write \(D'=D A,\ E'=E B\). The exact kernel for these terms is the \(T\)-kernel at \(z/D',z/E'\), multiplied by \(\rho(S/T)\). This factor combines with \(\rho(D)\rho(E)\) to give \(\rho(D')\rho(E')\), and \(q=T D'E'\). No multiplicity is introduced: from \(T,D',E'\) recover \(q\), its true full set \(S\), and \(A,B\) by their prime factors; dividing then recovers \(D,E\). Every prime \(\le z^2\,23/X\) is at most 19 or divides \(210\). Any one of \(11,13,17,19\) present in \(S\) lies in its first \(t\) elements, so \(D',E'\) satisfy the exact estimator's coprimality restriction. Its upper bound over all such integer outer rows therefore includes the merged blocks from all dimensions, as well as the original \(t\)-dimensional blocks, at the same cost. Smaller-dimensional rows retain their own estimates.

Any residual negative elementary term has one shared prime \(p\in S/T\), since double overlaps are favorable and triple overlaps impossible here. In the coefficient extraction of the preceding section, keep only terms with at least \(t\) other primes smaller than \(p\). This count is computed by a second polynomial index saturated at \(t\). For the lower endpoints use the maximum product of \(j\) other primes subject to that same restriction, by first taking the \(t\) largest below \(p\), then the largest \(j-t\) remaining. With \(t=3\), the same residual rule works without paying for a core since each fixed three-dimensional block has favorable sign.

| End | Exact dimensions through | Residual harmonic upper | Residual physical upper | Full clipping error including high tail |
|---:|---:|---:|---:|---:|
|100|6|\(7.18351\,10^{-8}\)|\(1.39933\,10^{-7}\)|.000005098007|
|121|6|\(1.79420\,10^{-7}\)|\(3.70345\,10^{-7}\)|.000010121108|
|200|5|.000010932730|.000020754323|.000064273|

For end 121 the exact lower-dimensional amounts are .000006044765 and .000003526578 (the full error uses their unrounded values); for ends 100 and 200 the exact values are given above. For \(q>X/100\) the preceding one-variable Liouville identity thus has additive error below **.000003343328** on the actual count.

~~~powershell
python -B round8/physical_low/rare_sign.py --end 100 --threshold 7 --anchor 6 --upper .0000000718351 .000000139933
python -B round8/physical_low/exact_wrong_sign.py --end 121 --maxdim 6 --upper .000006044765
python -B round8/physical_low/exact_wrong_sign.py --end 121 --maxdim 6 --physical --upper .000003526578
python -B round8/physical_low/rare_sign.py --end 121 --threshold 7 --anchor 6 --upper .000000179420 .000000370345
python -B round8/physical_low/rare_sign.py --end 200 --threshold 6 --anchor 5 --upper .000010932730 .000020754323
~~~
