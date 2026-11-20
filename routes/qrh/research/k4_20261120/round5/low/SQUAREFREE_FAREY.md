# A stronger interval sieve from removing squareful Farey denominators

For $x\ge0$ and $y\ge e^{70}$ the interval sieve of this project gives
\[
             \pi(x+y)-\pi(x)\le\frac{2y}{\log y+1.16613}.
\]
Retain the [correlated Farey argument](../../round4/low/CORRELATED_FAREY.md), $C=4/3$, $k=1.045$, $N=\lceil y\rceil+1$, $z=k\sqrt{N/C}$, $g=k^2$. Its weighted large sieve applies to any chosen set of distinct frequencies. Use only reduced fractions with **squarefree** denominator $q\le z$, including $0/1$. Every term used in the Ramanujan-sum lower bound is still present. The spacing to another retained fraction may increase. Write $M_q,M'_q$ for the average inverse spacing before and after removing the other denominators.

## Spacing after removal

For a reduced $a/q$, the original two Farey neighbors have denominators $b,b'$ with $b+b'\equiv0\bmod q$, the largest integers through $z$ in their respective unit classes. Put $u=q/z$, $\lambda=\{2z/q\}$, $x_0=(z-b)/q$, $y_0=(z-b')/q=\{\lambda-x_0\}$. The maximum initial inverse spacing is $q\max(b,b')$. On a side whose neighbor is removed, a replacement of determinant at least 2 has inverse spacing at most $qz/2$. Another of determinant 1 has denominator at most $b-q$ on the first side, and similarly on the other. Thus its *normalized* deficit from $z$ (divide the denominator deficit by $q$) is at least $c=\min(1,1/(2u))$ as well as its old deficit.

Let $Q=2310$, $d=(q,Q)$, and $\mathcal P$ be the primes dividing $Q/d$. Count a neighbor as removed when $p^2$ divides its denominator for some $p\in\mathcal P$. Let $R_1,R_2$ be the two resulting indicators. An additional lower bound on $(M_q-M'_q)/q^2$ is the reduced-residue mean of
\[
 R_1(\min(y_0,c)-x_0)_+
 +R_2(\min(x_0,c)-y_0)_+
 +R_1R_2(c-\max(x_0,y_0))_+ .
\]
The first two positive parts cannot both be positive. When both old deficits are below $c$ and both neighbors disappear, the last term pays for the second deficit up to $c$.

The variable $b$ runs through $(z-q,z]$ coprime to $q$. In a subinterval of normalized length $l$ and a fixed congruence class modulo $m$ coprime to $q$, its count differs from $\varphi(q)l/m$ by at most $2^{\omega(q)}$. This is inclusion-exclusion on divisors of $q$. Write $D_q=2^{\omega(q)}/\varphi(q)\le\sqrt{30/q}$ as in the original argument. Put $\kappa=1-\prod_{p\in\mathcal P}(1-p^{-2})$, $v=2^{|\mathcal P|}-1$. The first two superlevel sets each have at most two intervals. The two means together are at least $2\kappa I-4vD_q$, where
\[
 I=F(\lambda,c)+F(1-\lambda,(c-\lambda)_+),\qquad
 F(A,c)=A^2/4-(A-c)_+^2/2+(A-2c)_+^2/4 .
\]
Indeed $F(A,c)=\int_0^A(\min(A-2x,c-x))_+\,dx$; split at $x_0=\lambda$. It increases in both arguments. Always $I\ge1/24$. For $c=1/2,\lambda\le1/2$ it equals $\lambda^2/4+(1/2-\lambda)^2/2$ and for $\lambda\ge1/2$ its first term is at least $1/16$.

For the joint term split into the same two arcs, on which $b+b'=qj$ with $j=\lfloor 2z/q\rfloor$ or $j=\lfloor2z/q\rfloor-1$. For an eligible prime the residues of $b$ making $p^2\mid b$ or $p^2\mid b'$ number $v_p=1$ if $p^2\mid j$ and $2$ otherwise. CRT therefore gives joint removal density $\kappa_j=2\kappa-1+\prod_{p\in\mathcal P}(1-v_p/p^2)$. The level set on each arc is a single interval. Expand the two removal indicators separately: at most $v^2$ congruence terms occur, each inconsistent or a single class with modulus coprime to $q$. This joint contribution is at least
\[
 \kappa_j G(\lambda,c)+\kappa_{j-1}G(1-\lambda,(c-\lambda)_+)-2v^2D_q,\qquad
 G(A,c)=(c-A/2)_+^2-(c-A)_+^2 .
\]
Here the first $j$ denotes $\lfloor2z/q\rfloor$. The formula integrates $(c-\max(x,A-x))_+$ from 0 to $A$. At fixed $c$ it is unimodal in $A$ and increases in $c$. A coincident seam can be assigned either way in the area integrals; for the discrete classes take the half-open convention prescribed by $y_0=\{\lambda-x_0\}$ (the seam belongs to the first arc). The same discrepancy bound applies to any individual interval with specified half-open or open endpoints, using length and at most one unit per progression including a possible endpoint. Each nonnegative gain can be replaced by zero when its lower bound is negative.

## Counting denominators and transferring the improvement

Use $u\in(a,b]$ on a mesh of 4096, starting at $1/32$, and omit all smaller $u$. If $\lfloor2/u\rfloor$ changes, keep just the universal $I\ge1/24$. Otherwise take the two fractional endpoints $\lambda_-\le\lambda_+$ and $c_{\min}=\min(1,1/(2b))$. Monotonicity gives a lower bound by substituting $(\lambda_-,c_{\min})$ and $(1-\lambda_+,(c_{\min}-\lambda_+)_+)$ in the two $F$ terms. Minimize each $G$ at the endpoints of its $A$ interval with the lower $c$. Use $\sqrt{30/(az_0)}$ for every $D_q$, where $z_0=k\sqrt{e^{70}/C}$.

Let $\delta=\varphi(Q)/Q$, $b_*=\zeta(2)\prod_{p\mid Q}(1-p^{-2})-1$. Write $q=dn$ with $(n,Q)=1$ and $n$ squarefree. Inclusion-exclusion counts all such $n$ without the squarefree condition to within $2^{\omega(Q)}$. Subtract counts of multiples of $p^2$ for $p\nmid Q$, using $\sum p^{-2}\le b_*$ and at most $\sqrt{bz/d}$ relevant primes. The count of admissible $q$ divided by $z$ is at least
\[
 \delta(1-b_*)\frac{b-a}{d}
   -2^{\omega(Q)}\left(\frac1{z_0}+\sqrt{\frac{b}{d z_0}}\right).
\]
For each $q$, $1/\varphi(q)\ge d/(\varphi(d)bz)$. If the old normalized deficit is at least $D$ (from (3) of the previous proof) and the new gain in that deficit is at least $E$, the increment in the summand of $\mathcal H$, divided by $1/\varphi(q)$, is at least
\[
 \frac{g a^2 E}{(1+ga-ga^2D)(1+ga-ga^2(D+E))}.
\]
To replace $u$ by $a$ divide both denominator factors by $u$; the resulting positive factors decrease with $u$. The script verifies denominator positivity at the bound; the geometric bounds themselves ensure it for actual spacings throughout. The class $d=Q$ has no eligible primes and needs no charge.

Summed in $2\mathcal H$, the [192-bit verifier](squarefree_farey.py) gives an increment exceeding **.03333283** on top of the old proof with all denominators. That proof had already reserved $.00004$ for replacing $N$ by the interval length and for small primes. Its transfer estimates continue to apply since $1.16613+.00004<2$. This proves the displayed sieve inequality without a zeta-zero hypothesis.

For the prime-interval application use the [physical sidelobe proof](PHYSICAL_TAIL.md) with this stronger sieve, $K=H-206000$ and the original Gaussian width $10000$. The negative-extension branch of its inherited formula charges all unverified heights with the unrestricted Gaussian tail. On the complete closed cells $[115.033660,115.034610]$ and $[115.034610,115.034625]$, the angular/level meshes are respectively $512/256$ and $1024/512$. Their total upper bounds are less than $.999996575$ and $.999998490$. They join the previous coverage at $115.033660$. Hence, using the listed published inputs and the derived sieve bounds, every integer $n\le3\,088\,344\,337\,091$ has a prime between $n^4$ and $(n+1)^4$, independently of QRH. [Whole-slab replay](squarefree_cover.py)

~~~sh
python -B round4/low/correlated_farey.py
python -B round5/low/squarefree_farey.py
python -B round5/low/squarefree_cover.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived the squarefree-frequency sieve improvement.
