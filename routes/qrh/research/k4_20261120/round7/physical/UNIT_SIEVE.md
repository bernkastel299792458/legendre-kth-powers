# Sieving on the units of a fixed primorial

## Spacing of the reduced rational frequencies

In a grouped block write \(n/w=A/B\) in lowest terms. Every representation has \((n',w')=(Aj,Bj)\), where \((j,P)=1\) since the physical row vanishes unless \((w',P)=1\). For the even moduli in use the possible \(j\)'s have spacing at least two. The multiplicity is thus at most \(1+(J-N)(n,w)/(2n)\). For the term with a divisor \(r>1\) in the gcd expansion, the row count is zero unless \((r,P)=1\). The remaining \(w/r\)'s are units in a half-open interval of length \(F/(2r)\). If \(\eta,\Delta\) are the unit density and real-endpoint discrepancy, the old bound \(F/r\) may therefore be multiplied by \(\min(1,\eta/2+\Delta J/F)\), since \(r\le n\le J\). The term at \(r=1\) uses its actual squared row energy.

For every divisor \(s\) of the surviving numerator sieve, both numerator and denominator are units modulo \(s\). Partition the distinct rationals by \(n/w\bmod s\). Within each of at most \(\varphi(s)\) classes the nonzero cross determinant is a multiple of \(s\), so frequency separation increases by a factor \(s\). Cauchy across the classes multiplies squared mass by at most \(\varphi(s)\). In the [grouped Paley estimate](extras/GROUPS.md) take the least of the old frequency factor and \(\varphi(s)\max(1/(sK_0),1/(bF))\) for each \(s\). The sampling variable may independently use its earlier residue-class bounds. This argument applies to arbitrary coefficient phases after each frequency is merged.

The sharp endpoint option computes \(g(u)=\tfrac12\operatorname{sinc}((u+a)/2)\operatorname{sinc}((u-a)/2)\). The moving derivative factor in the first lobe is bounded by the two endpoint moduli of \(g'\), the integral of \(|g''|\), and \(F_0/K\). The 128 midpoint panels use \(|g'''|\le\int_0^1 v^3(1-v)\,dv=1/20\), by the [sine integral](WEIGHTED_LOBE.md). Sinc and its first two derivatives are enclosed by their power series through \(j=16\); for arguments of modulus at most four the tail is at most twice its first absolute term. The first-lobe area uses the trapezoid bound with \(|g''|\le1/12\). The secondary lobes use the rational expression for \(g''\) on 64 interval panels apiece. All the outward endpoint comparison and root-height charges of the earlier proof are retained. For the optional two-uniform endpoint average take displacements of lengths \((1-\lambda)\ell,\lambda\ell\), \(\ell=e^{l-r-\epsilon/K}\epsilon/K\), summed in the inward physical direction. This lies within the prime-free interval, increases mean length by at most the original allowance, and yields factors \(\min(1,m/(\pi n(1-\lambda)\ell))\) and \(\min(1,m^2/(\pi^2 n^2\lambda(1-\lambda)\ell^2))\). The second factor can use the retained \(n^{-2}\) row after contraction by \(N/n\). The connected rows below use the single-uniform endpoint.

For a location ceiling of 116 the six previously proved [denominator additions](extras/GROUPS.md) exceed 8. The six earlier entries actually used in the lobe transfer are smaller than 8, so all of those transfers remain valid at this wider location ceiling. Each of the following intervals overlaps the recorded preceding range. Under QRH the complete budget is below .998779 on \([115.382,115.389]\) and below .999740 on \([115.389,115.402]\). With unrestricted high zeros it is below .999946 on \([115.375,115.382]\) and below .999693 on \([115.380,115.384]\).

~~~powershell
python -B round7/physical/grouped_lobes.py --lo 115.382 --hi 115.389 --ratio 96 --secondary-ratio 121 --inside .0014 --modulus 30 --exact-harmonics --sparse --sharp-variation --qrh --check
python -B round7/physical/grouped_lobes.py --lo 115.389 --hi 115.402 --ratio 138 --secondary-ratio 146 --inside .0016 --modulus 30 --exact-harmonics --sparse --sharp-variation --location-hi 116 --qrh --check
python -B round7/physical/grouped_lobes.py --lo 115.375 --hi 115.382 --ratio 85 --secondary-ratio 122 --inside .0013 --modulus 30 --exact-harmonics --sparse --sharp-variation --check
python -B round7/physical/grouped_lobes.py --lo 115.380 --hi 115.384 --ratio 91 --secondary-ratio 120 --inside .0013 --modulus 30 --exact-harmonics --sparse --sharp-variation --check
~~~

## Exact harmonic support and smoothing the first endpoint

Let \(M=P/2\). For the absolute Ramanujan weight, partition its Fourier index \(v\) according to \(m=(v,M)\). Then \(v=mj,\ (j,M/m)=1\), the dilation is \(P/m\), and the coefficient per \(1/j\) is \(\varphi(m)/m\). This keeps every original sign in each separately bounded transform. The large-frequency \(1/j^2\) tail can drop the restriction on \(j\). For each finite block discard missing endpoints. Compute its exact count and harmonic moment by inclusion–exclusion and digamma differences; the second moment uses the same differences of Hurwitz zeta at 2. For a divisor \(r\mid j\) with \((r,P)=1\), the complementary factor is also a unit modulo \(M/m\). Thus the hyperbola bound for grouped frequency collisions can impose this latter restriction as well. The normalized coefficient of the differentiated phase uses the exact surviving count divided by the harmonic sum. All index and harmonic bounds used in the block Cauchy estimate apply also when its coefficients carry arbitrary phases of modulus at most one.

For the whole first pair of exterior lobes choose an internal endpoint averaging width as before. With the exact harmonic partition and width .001, the conditional cost on \([115.374,115.382]\) is below .998625 at the indicated ratio pair. The width .0013 with unrestricted zeros above the published verification gives a cost below .998639 on \([115.368,115.376]\).

~~~powershell
python -B round7/physical/grouped_lobes.py --lo 115.374 --hi 115.382 --ratio 84 --secondary-ratio 118 --modulus 30 --inside .001 --exact-harmonics --qrh --check
python -B round7/physical/grouped_lobes.py --lo 115.368 --hi 115.376 --ratio 84 --secondary-ratio 119 --modulus 30 --inside .0013 --exact-harmonics --check
~~~

For the tail sum of the absolute Selberg numerators, the exact convolution is \(\sum_{n\le z,(n,P)=1}\mu^2(n)\sigma(n)/\varphi(n)\). The old finite-prime density argument now uses average \(1-1/p\) and divisor-polynomial coefficient norm 2 at \(p\mid P\). These primes remove their old factors \(1+1/p^2\) from the mean. This is an additional upper-bound improvement at the finite harmonic cutoff.

Let \(P\in\{2,6,30,210\}\), \(\eta=\varphi(P)/P\), and
\[
 G_P(v)=\sum_{n\le v,(n,P)=1}\frac{\mu^2(n)}{\varphi(n)}.
\]
All primes in the tested physical intervals exceed both \(z\) and every prime factor of \(P\). On the units modulo \(P\) use
\[
 \lambda_d=\frac{\mu(d)d}{\varphi(d)G_P(z)}G_{Pd}(z/d)
 \quad ((d,P)=1,\ d\le z),
\]
with zero elsewhere. Apply the [Selberg square identity](BILINEAR.md) on the divisor-closed set of these indices. Its quadratic main coefficient is \(1/G_P(z)\). Counting only multiples of \(q=[d,e]\) with multiplier coprime to \(P\) therefore gives the main coefficient \(\eta/G_P(z)\). Also \(|\lambda_d|\le1\), since each \(ab\) with \(a\le z/d,(a,Pd)=1,b\mid d\) contributes to \(G_P(z)\).

## Explicit denominator

Set \(1*b(n)=\mathbf1_{(n,P)=1}\mu^2(n)n/\varphi(n)\). For \(p\mid P\), \(b(p)=-1\) and all higher local coefficients vanish. For \(p\nmid P\) the nonzero coefficients are \(b(p)=1/(p-1)\) and \(b(p^2)=-p/(p-1)\). Put \(s=3/4,\ B=\sum |b(n)|n^{-s}\). The [replay](odd_sieve.py) sums its Euler factors through 1000. The rest has logarithm at most \(1.001(1000^{-s}/s+1000^{1-2s}/(2s-1))\) by comparison with the sum over all integers.

Use \(G_P(z)=\sum_{n\le z} b(n)H_{\lfloor z/n\rfloor}/n\). On \(t\ge1\), \(|H_{\lfloor t\rfloor}-\log t-\gamma|\le2/t\) by integral comparison. On \(0<t<1\) the modulus of \(\log t+\gamma\) is at most \((\gamma+1/(e(1-s)))t^{s-1}\). Extending the logarithmic main term to all \(n\) gives
\[
 \left|G_P(z)-\eta\left(\log z+c_0+\sum_{p\mid P}\frac{\log p}{p}\right)\right|
 \le (2+\gamma+1/(e(1-s)))Bz^{s-1}.
\]
Indeed \(\sum b(n)/n=\eta\), and taking out the factor \(1+p^{-w}/(p-1)\) from \(\sum\mu^2(n)n^{-w}/\varphi(n)\) changes its constant term by \(\eta\log p/p\) after multiplying the original terms by \(\eta\). Equivalently, logarithmically differentiate the finite product of these reciprocal factors at \(w=0\). We use \(1.33258<c_0<1.332583\). [Ramaré, Theorems 1.3 and 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/113104)

## Fourier error

The number of admissible multipliers \(k\le t/q\) is the sum of the counts on the \(\varphi(P)\) residue classes. Its nonzero sawtooth coefficients at frequency \(n\) acquire the real Ramanujan factor \(c_P(n)=\sum_{a\bmod P,(a,P)=1}e^{-2\pi i n a/P}\), and their phase becomes \(2\pi nt/(Pq)\). Both endpoints are averaged continuously as in the [grouped bound](GROUPED_LOBE.md). The constant endpoint terms cancel. For squarefree \(P\),
\[
 |c_P(n)|=\prod_{p\mid P}(1+(p-2)\mathbf1_{p\mid n}).
\]
Expand the product over divisors \(m\) and write \(n=mj\). Each resulting series is estimated in the frequency \(j\), with dilation \(D=P/m\) and coefficient \(\prod_{p\mid m}(p-2)/m\). The remaining sign has modulus one and depends only on \(j\). The frequency-group Cauchy bound uses squared moduli after merging equal rational frequencies and applies to these signs. The phase-scale and endpoint-difference bounds divide by \(D\), and the two endpoint integration-by-parts bounds multiply by \(D\). The absolutely convergent remainder beyond \(j=2^{48}\) is included separately for each divisor.

In both original rows with indices \(d=ghx\) and \(e=ghv\), shared singleton factors divisible by a prime of \(P\) are absent. The [second moment proof](extras/WEIGHT_ENERGY.md) restricts the residue masks and numerator harmonic sums by inserting \(P\) into their coprimality test. The factor bounding \(gh/\varphi(gh)\) is unchanged. Unknown shared factors may retain their old upper bounds. The tails obtained from \(|\lambda_d|\le1\) still apply. The bound on \(z^{-1}\sum |\lambda_d|\) uses the previous unrestricted positive numerator divided by the new lower bound for \(G_P(z)\).

Both variable indices \(x,v\) are odd. If \(D_x,D_v\) denote the old dyadic dimensions, the physical sampling points \(D_x/x\) have separation at least \(2/D_x\). The single-frequency reciprocal points have separation at least \(2K_0/D_v\); distinct rational frequencies in the grouped version retain the earlier \(K_0/D_v\) lower bound. Thus the first factor \(1+(K+b)/D_x\) in the [sampling estimate](extras/GROUPS.md) can be replaced by \(1/2+(K+b)/D_x\); the factor \(1/K_0\) in its maximum can also be halved in the single-frequency case. The direct counts are at most \(D_x/4+1,D_v/4+1\). All other estimates for positive lobes, exterior tails, zeros and prime powers are retained. The option `--modulus P` selects the indicated square for both treated groups of lobes.

For any divisor \(m\) of \(P\), split the outer physical sum into its \(\varphi(m)\) unit residue classes. Each class has spacing at least \(m/D_x\), so the sampling factor is at most \(\varphi(m)(1/m+(K+b)/D_x)\). At a single harmonic its inner sum can independently be split into classes modulo \(m'\mid P\). Cauchy across the classes multiplies the squared bound by \(\varphi(m')\), and the separation in each is at least \(m'K_0/D_v\). Take minima of these positive upper bounds. The suprema for the numerator harmonic sum may also use the two-sided convolution estimate above; the maximum of \(d/\varphi(d)\) over unit integers below a given bound occurs at a product of the smallest allowed primes.

The following four replays certify connected ranges. The unconditional rows meet the earlier finite-height interval at 115.290. The QRH rows also overlap at their endpoints with earlier coverage.

| Modulus | Closed range | Input above verified height | Complete cost below |
|---:|---|---|---:|
| 2 | [115.290, 115.320] | unrestricted | .9980 |
| 2 | [115.318, 115.333] | unrestricted | .9980 |
| 2 | [115.297, 115.331] | QRH(7/8) | .995543 |
| 2 | [115.329, 115.345] | QRH(7/8) | .999778 |

~~~sh
python -B round7/physical/grouped_lobes.py --lo 115.290 --hi 115.32 --ratio 100 --secondary-ratio 110 --modulus 2 --check
python -B round7/physical/grouped_lobes.py --lo 115.318 --hi 115.333 --ratio 110 --secondary-ratio 115 --modulus 2 --check
python -B round7/physical/grouped_lobes.py --lo 115.297 --hi 115.331 --ratio 105 --secondary-ratio 120 --qrh --modulus 2 --check
python -B round7/physical/grouped_lobes.py --lo 115.329 --hi 115.345 --ratio 110 --secondary-ratio 120 --qrh --modulus 2 --check
~~~

The following refinements keep the same Selberg square. In a nonsingleton block \([a,b]\) of shared factors, calculate the mass \(\sum_{a\le j\le b,(j,P)=1}\mu^2(j)/j^2\) directly through \(b<8192\). Beyond it, count only unit integers surviving the square divisibility tests for \(2,3,5,7\). This is periodic modulo \(210^2\). Its exact integer-endpoint discrepancy \(\Delta\) and density \(\eta_1\) give the upper bound \(\eta_1(1/a^2+1/a-1/b)+\Delta/a^2\) by summation by parts.

Also order all the units modulo \(P\) on the full integer line and split by the rank modulo \(k\). Each class has separation at least the least distance from a unit to the \(k\)-th subsequent unit. It is found by inspecting the finite period twice. For distance \(d_k\), this gives sampling factor \(k/d_k+k(K+b)/D_x\) and, for a single harmonic, frequency factor \(k\max(1/(d_kK_0),1/(bD_v))\). Use the least of these bounds. For the direct counts also use density \(\varphi(P)/P\) times the half-dyadic length, plus the full real-endpoint discrepancy from the same period.

Finally, in the grouped frequency multiplicity estimate decompose \((n,w)=1+\sum_{r\mid n,\ r\mid w,\ r>1}\varphi(r)\). Pay the first term with true row energy. The others have \((r,P)=1\) and at most \(D_v/r\) multiples in the row. Compute \(\sum_{r\mid n,(r,P)=1,r>1}\varphi(r)/r\) through \(n=4096\). On a longer group \(N\le n\le J\) of length \(l\), split \(n=rm\) at \(S=\lfloor\sqrt J\rfloor\). The triangle \(r\le S\) admits at most \(l H_P(S)+\eta S+\Delta\) pairs, with \(H_P(S)\le\eta(1+\log S)+\Delta\). The triangle \(m\le S\) contributes at most \(l\eta(1+\log S)+S\Delta\), by the same unit-interval discrepancy. Subtract the \(l\) pairs with \(r=1\) after taking the minimum with the unrestricted pair bound. The estimates apply independently of the Ramanujan signs.

Closed intervals beyond the preceding table have been bounded with the following choices. The first three rows allow arbitrary zeros above the verified height.

| Modulus | Closed interval | High-zero input | Parameters, first and secondary | Full cost below |
|---:|---|---|---|---:|
| 2 | [115.329, 115.345] | unrestricted | 130, 140 | .998440 |
| 6 | [115.340, 115.361] | unrestricted | 97, 113 | .997903 |
| 30 | [115.355, 115.370] | unrestricted | 87, 99 | .999469 |
| 6 | [115.340, 115.366] | QRH | 92, 100 | .998331 |
| 6 | [115.358, 115.372] | QRH | 102, 116 | .998965 |
| 30 | [115.371, 115.376] | QRH | 84, 94 | .999396 |

Use the two endpoints as the arguments to \(\verb|--lo|\) and \(\verb|--hi|\), both parameter values as \(\verb|--ratio|\) and \(\verb|--secondary-ratio|\), and the tabulated \(\verb|--modulus|\) with \(\verb|--check|\). Include \(\verb|--qrh|\) only for the indicated rows. Older rows can also be replayed in the local research history with their recorded upper bounds.
