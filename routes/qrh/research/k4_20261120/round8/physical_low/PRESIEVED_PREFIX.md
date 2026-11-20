# Complete presieved large-modulus prefix at L=116

Let \(Q=210,\ x=e^{116},\ K=H,\ z=1732099\sqrt{x/H},\ X_\pm=e^{c\pm2r},\ r=10^{-6}\), with the near physical region \(|v|\le r\). In [the full normalization](unit_budget.py), the ordinary main term and terms outside the near-prime remainder are bounded by .983484173844 and .000001755341. Two separate choices for the cutoff give the following. The last column is a sufficient remaining allowance, rounded **down**.

| Cutoff on the low moduli | All actual multiples above it | Absolute signed inverse moment above it | Combined upper charge | Remaining allowance |
|---|---:|---:|---:|---:|
| \(q\le X_+/23\) | .012803518958 | .000132328068 | .012935847025 | .0035782237 |
| \(q\le X_+/29\) | .015391593974 | .000139050451 | .015530644424 | .0009834263 |

The full inverse column already includes the inverse contribution of the empty band \(q>e^{c+r}/11\). In particular the empty cost in the earlier table is not added again. Neither row yet bounds the remaining low moduli. All true multipliers are included: they are \(11,13,17,19\) at cutoff 23 and additionally \(23\) at cutoff 29. Both the actual spike and the inverse refer to the same region.

## Counting all squarefree divisor pairs in the actual spikes

Write \(d=gu,\ e=gv\), with \(g=(d,e)\), so that \(q=guv\), \((u,v)=1\) and all indices are coprime to \(Q\). They are squarefree whenever their coefficients are nonzero. The exact product of absolute coefficients expands over \(b,t\) with weights
\[
 \frac{\rho(g)^2\rho(u)\rho(v)}{G_Q(z)^2\varphi(b)\varphi(t)}.
\]
Here \(b,t\) are squarefree and coprime to \(gQ\), \((b,u)=(t,v)=1,\ gu b\le z,\ gv t\le z\). When \(kq\) belongs to a near interval, \(X_-<kguv<X_+\). Hence \(gbt<k\) since \(z^2<X_-\); every \(g,b,t\) is in the finite enumeration. At fixed \(k,g,b,t\), use \(A=X_-t/(kz),\ B=z/(gb)\) and \(\ell=\log(B/A)\), retaining nonempty rows. The outer \(u\)-range is \((A,B]\) and the inner \(v\)-interval has length at most \(y/(kgu)\). Relaxing any remaining size restrictions on that interval only increases the bound. Symmetry allows the orientation with smaller \(B\) for \(b\ne t\).

Take \(P=37\). At \(p\le P\), the positive profile is the exact local squarefree weight \(w_p\), with the restrictions on both variables and their joint gcd. Call the \(u\)-side forced if \(p\mid Qgb\), and the \(v\)-side forced if \(p\mid Qgt\). A forced side must be a unit at \(p\). Write \(h_p=1-1/p\). The local two-variable mean is \(h_p^2,h_p\), or \(1-1/p^2\), according as both, one, or neither side is forced. In the last case this follows by subtracting the weight \(1/p^2\) of two variables both at valuation one from their unrestricted weighted mean one. Let \(\delta\) be the product of these local means.

For fixed \(u\), the inner small-prime profile has discrepancy at most \(D=2^{\pi(P)}U\), \(U=\prod_{p\le P,\,p\nmid Q}\rho(p)\), by its divisibility expansion. Its mean times the outer small-prime weight is also an outer divisibility polynomial of coefficient norm at most \(D\): at a forced inner prime it is \(h_p\) times the appropriate outer local weight, while at a free inner prime it is either an indicator of being prime to \(p\) or one of being squarefree at \(p\). Its mean is \(\delta\). Small-prime coprimality is therefore retained on the physical short interval.

At \(p>P\), enlarge the weights by dropping squarefree and coprimality exclusions and using \(\prod_{p\mid n,p>P}(1+1/(p-1))\). The resulting divisor convolution has reciprocal mass at most
\[
 T=\prod_{P<p\le1000}(1+1/(p(p-1)))e^{1/1000}
\]
and unweighted mass through \(z\) at most \(F=(1+\log z)^2\). Conditioning on any such divisor preserves the small-prime discrepancy. Partial summation over \(A<u\le B\) gives a slope at most \((\delta T^2\ell+DFT/A)/(kg)\). For the inner discrepancy, the whole outer unweighted mass is bounded by \(UT B\), using \(\lfloor B/d\rfloor\le B/d\) for each positive large-prime divisor coefficient. Thus the intercept is at most \(DFUT B\). Multiply both bounds by \(\rho(g)^2/[G_Q(z)^2\varphi(b)\varphi(t)]\), with \(G_Q(z)\ge(\varphi(Q)/Q)(\log z+1.331)\).

For a cutoff \(m\), all actual \(k>1\) are precisely the candidates \(k<m,\ (k,Q)=1\), since the program verifies \(X_-/k>X_+/m\) separately for each retained \(k\). The multiplier 1 is impossible. Sum their slope coefficients against total exterior area and the intercepts against the total summed peaks, in the same normalization as [the empty-modulus argument](PRESIEVED_EMPTY.md). The signed inverse correction over \(q>X_+/m\) uses its curved-region proof and the optional finite mean Mertens table. The positive multiple count itself is unconditional. The resulting costs from all actual \(k\), including every possible \(g>1\), are respectively .003649139, .003362311, .002969694, .002822377 and .002588076 in increasing order. The estimates do not require cancellation between different true multiples.

~~~powershell
python -B round8/physical_low/unit_budget.py
python -B round8/physical_low/presieved_prefix.py --Q 210 --next 23 --mean --rows --upper .012935848
python -B round8/physical_low/presieved_prefix.py --Q 210 --next 29 --mean --rows --upper .015530645
~~~
