# Smoothing the cutoff and retaining the fourth harmonic

Use the setup of [the periodic approximate functional equation](PERIODIC_FOURTH.md) with \(a=\alpha\sqrt Q,\ b=\sqrt Q/\alpha,\ z=\sqrt{t/(2\pi)}\). Introduce \(u\) uniform on \([-w,w]\), \(w>0\), and replace the two cutoffs by \(ae^u z,\ be^{-u} z\). Simonič's Corollary 1 and Table 2 give the same remainder upper bound as before multiplied by \(e^{w/2}\), now with the exact elementary multiplier \(\widetilde\chi(1/2+it)=\exp[-it\log(t/(2\pi e))+i\pi/4]\). Take the lower starting height \(t_0\ge1000\) such that \((\max(a,b)e^w)^2\,2\pi\le t_0\), so every \(x_d,y_d\ge1\). For \(200\le t\le t_0\), the symmetric Riemann–Siegel bound gives \(4(t_0/(2\pi))^{1/4}+1\) for \(|\zeta|\), with 17 retained at \(t_0=1000\). [Simonič, equations (11)–(13), Table 2](https://arxiv.org/pdf/1910.08274#page=4)

There are two valid estimates. In the unpaired estimate, average the two Dirichlet polynomials first and then use their fourth norms. In the paired estimate the \(L^4\) space has measure \(dt\,du/(2w)\), and the pointwise AFE is used before taking the average. The latter keeps the two cutoffs paired in the fourth harmonic. Denote the respective positive frequency polynomials by \(A_u,B_u\); the coefficients are the unit indicator and \(c_Q(n)/\sqrt Q\), both with the phase \(n^{-it}\).

## The smoothed individual fourth norms

In either branch let \(\sigma\) be its central length multiplier times \(e^w\), \(Y=\sigma\sqrt{T/(2\pi)}\), \(Y_0=\sigma\sqrt{e^U/(2\pi)}\). For one raw index \(n\) its mean indicator \(g_n(t)\) is 0 below \(t_n=2\pi(n/\sigma)^2\), 1 above \(e^{4w}t_n\), and linear in \(\log t\) between these points. For a quadruple with largest index \(m\), the paired expansion at common \(u\) has time weight \(G=g_m\). The unpaired expansion has \(G=\prod_i g_{n_i}\). Integrate the nonnegative entire fourth norm from zero to \(T\) for an upper bound on the range \([t_0,T]\). The [previous diagonal envelopes](PERIODIC_FOURTH.md) apply at \(Y\). In the paired case take each sharp arithmetic sum at its true cutoff before the average and bound its squared prefix by the running peak used in that proof. In the unpaired case the two inner factors \(g_{gr}g_{gs}\) are decreasing in \(g\) with values in \([0,1]\); hence their weighted signed inner sum is dominated by the same absolute running peak by Abel summation. Below \(T_*=2\pi Z^4/\sigma^2\) the elementary bulk upper bound already covers the entire time interval from zero; the bound on the absolute continued polynomial is needed only on \([t_0,T_*]\). The code parameters have \(t_0<T_*<e^U\).

For an off-diagonal frequency \(\lambda=\log(n_1n_2/(n_3n_4))\), integration by parts yields the upper endpoint \(G(T)e^{iT\lambda}/(i\lambda)\) and a residual integral with \(G'\) divided by \(i\lambda\). The total mass of \(G'\) is at most one. For paired cutoffs, \(G'=1/(4wt)\) on one interval, whose oscillatory integral has modulus at most \(2/(4w t_m|\lambda|)\) by a layer-cake comparison over intervals. For unpaired cutoffs, sum four terms with an additional nondecreasing product of the three other weights inside each term. All contributing times are at least \(t_m\). Superpose the upper intervals of the nondecreasing product with the lower intervals of \(1/t\) to obtain the same bound four times. If \(h=|n_1n_2-n_3n_4|>0\), then \(t_m|\lambda|\ge2\pi h/\sigma^2\). The residual coefficient is therefore at most
\[
 \frac1{|\lambda|}\min(1,J/h),\quad
 J=\sigma^2/(4\pi w)\quad\text{(paired)},\qquad
 J=\sigma^2/(\pi w)\quad\text{(unpaired)} .
\]

With the notation \(F,S\) of the periodic estimate use the near-shift count on the whole positive range. For \(G_0=\gcd(i,k),\ n=h/G_0\), majorize \(\min(1,J/h)\le\min(1,J/n)\). For \(j\bmod Q\) let \(b_j\) bound \(\sum_{n\equiv j\bmod Q,n\ge1}\min(1,J/n)/n\). Round \(J\) up to the next \(1/1024\), sum through \(\max(128Q,\lfloor J\rfloor+1)\), then bound the tail from the first remaining \(n\) by \(J(1/n^2+1/(Qn))\). Put \(D_J=\max\sum_j d_j b_j,\ R_J=\max\sum_j r_j b_j\) over all allowed step pairs. The residual cost divided by \(Y^2\) is at most
\[
 2(FD_J+SR_J)+16(.118)\,[m+D/(2\sqrt{Y_0})]^4 ,
\]
where \(m,D\) are the mean and discrepancy of the absolute coefficient sequence. The .118 bound was proved in the [off-diagonal proof](../../round5/left/OFF_FOURTH.md).

## Hilbert bound at the common upper endpoint

At a fixed cutoff, write \(b_n=\sum_{ij=n}v(i)v(j)\) with the active indices only, allowing the corresponding real taper factors in the unpaired case. For the paired estimate bound the endpoint for each \(u\) and then average. The generalized Hilbert inequality used in the proof of Chourasiya–Simonič Lemma 10 bounds this single endpoint by
\[
 \frac{\pi\,1.31541}{g}\left[\sum_n b_n^2+\sum_n b_n^2/n\right]
\]
with \(g=2\) for units (only odd products) and \(g=1\) for the dual. Indeed the log-frequency gap reciprocal is at most \(n/g+1/2\); the displayed bound includes this term for both values of \(g\). The complex phase at \(T\) has modulus one. A crude bound for the harmonic sum is \(\|v\|_\infty^4(1+\log Y)^4\), by the two-ratio equal-product parameterization. [Chourasiya–Simonič, Lemma 10 and its proof using Preissmann's inequality](https://arxiv.org/html/2507.15184v2#S5.SS1)

To bound \(Y^{-2}\sum b_n^2\) write the equal products as in the diagonal proof, now without the \(1/(rs)\) weights. For each outer pair of residue classes \(h,k\), define \(w(i)=v(ih)v(ik)\) and \(V_j=\max_{0\le n\le j}|\sum_{i\le n} w(i)|^2\). The taper case has the same upper bound by monotonicity in the inner integer. Write \(N_h(x)\) for the raw class count and choose its one-sided bound \(N_h(x)\le\rho_h x+D_h\). The finite prefix through \(K=\max(2Q,192)\) costs at most
\[
 \sum_{j\le K}(V_j-V_{j-1})
            (\rho_h/j+D_h/Y_0)(\rho_k/j+D_k/Y_0).
\]
All zero-mean inner classes have periodic partial sums, so this already covers their full contribution. Only the unit/unit class can have nonzero mean \(\mu\). With \(X=Y/(K+1)\), its residual is at most
\[
 \mu^2\sum_{M\le X}M^{-2}
       +2\mu D\,Y^{-1}\sum_{M\le X}M^{-1}+D^2 N_1(X)^2/Y^2,
\]
where \(M=\max(r,s)\) with both integers units and \(D\) bounds the upper discrepancy for the inner \(w=v^2\) count. This bound may count the initial \(V_K\) again. Writing \(\rho=\rho_1,\ d=D_1,\ X_0=Y_0/(K+1)>K\), the first sum is bounded exactly through \(K\); the addition is at most
\[
 (\rho+d/X_0)^2-N_1(K)^2/K^2+
 2\rho^2\log(X/K)+4\rho d/K+d^2/K^2 .
\]
This is partial summation of \(N_1(t)^2\). The second normalized count \(Y^{-1}\sum_{M\le X}1/M\) is bounded in turn by \(2\rho^2/(K+1)+[2\rho d(1+\log X_0)+2d^2]/Y_0\). The last factor \(N_1(X)/Y\) is at most \(\rho/(K+1)+d/Y_0\). Thus the endpoint divided by \(T\) is bounded by an affine polynomial in \(\log T\), plus a uniformly bounded harmonic correction.

The period scan uses exact signed 64-bit integers, with an explicit bound checked on every accumulator. For reduced steps \(P,S\) and residue \(n\), one particular solution \(Px-Sy=1\bmod Q\) supplies the orbit \((nx+Sj,ny+Pj)\). The coefficients are invariant under sign changes in the two variables. Changing either step sign reverses the parameter or reflects one variable; neither operation changes its interval discrepancy or mean. Interchanging the steps exchanges the two variables and sends \(n\) to \(-n\), which has the same data by reflection of both variables. It therefore suffices to scan \(0\le P\le S\le Q/2\). At each interval the mean times \(Q\) and the discrepancy times \(Q\) are integers. All harmonic upper constants multiplying these nonnegative quantities are first rounded upwards to millionths.

## Mixed fourth harmonic

Fix one \(u\), \(x=ae^u\sqrt{t/(2\pi)}, y=be^{-u}\sqrt{t/(2\pi)}\), and absorb \(Q^{-1/2}\) into the raw dual polynomial at the end. The phase in the mixed second power is \(e^{i\phi}\) where \(\phi=t\log(Qt/(2\pi e))-\pi/4\). We bound the mixed fourth harmonic \(\int e^{2i\phi}A_u^2B_u^2dt\). There are no stationary frequencies beyond the moving endpoint, since \(x^2y^2=(Qt/(2\pi))^2\). Let \(t_e=T^\nu,\ \nu=.48\) and \(H=\sqrt T\). For \(t_e\le t\le T\) shift the contour on each constant-cutoff segment from \(t\) to \(t+iH\). The phase \(\Psi(z)=2z\log(Qz/(2\pi e))\) is analytic in the right half-plane and
\[
 |e^{i\Psi(t+iv)}|\le (Qt/(2\pi))^{-2v}=(xy)^{-2v}\quad(v\ge0).
\]
Indeed \(\partial_v\Im\Psi(t+iv)=2\log|Q(t+iv)/(2\pi)|\). This bound distributes precisely two powers \(x^{-v}\) and two \(y^{-v}\) among the polynomials. All bounds here are uniform in \(u\).

For \(j=f,d\), let \(\tau_j\) be the unit indicator or the absolute raw Ramanujan sequence, respectively. Write \(m_j,D_j\) for its mean and interval discrepancy, and \(l_j,h_j\) for the minimum and maximum allowed cutoff divided by \(\sqrt t\). Thus \(l_f=ae^{-w}/\sqrt{2\pi}\), etc. At a cutoff \(X\in[l_j\sqrt t,h_j\sqrt t]\) set
\[
 S_{j,v}(X)=\sum_{n\le X}\tau_j(n)n^{-1/2}(n/X)^v.
\]
For \(0\le v\le1/2\), integration of the nonincreasing power gives \(S_{j,v}\le m_j\sqrt X/(v+1/2)+D_j X^{-v}\). For \(v\ge1/2\) the power is nondecreasing and the correction is at most \(D_j/\sqrt X\). Both follow by interval layer-cake. For \(t\ge t_e\) put \(M_j=m_j+D_j l_j^{-1/2}e^{-\nu U/4}\), \(c=\max_j D_j/(m_jl_j)\). It follows that
\[
 S_{j,v}(X)\le M_j\sqrt X\,[1/(v+1/2)+c/\sqrt t].
\]
The omitted initial times \(t\in[t_0,t_e]\) contribute, after division by \(QT\), at most
\[
 e^{(2\nu-1)U}Q^{-1}\prod_j(2m_j\sqrt{h_j}+D_j e^{-\nu U/4})^2
\]
by bounding the increasing unweighted sum at \(t_e\). Here and below \(Q^{-1}\) normalizes the two dual factors.

Write \(C=M_f^2M_d^2/(2\pi)\). The top horizontal contour divided by \(QT\) is at most \(C(1+c)^4 Ue^{-U}\) on integrating \(dt/t\), since \(1/H\le1/\sqrt t\). Let \(d_e=c e^{-\nu U/2}\). Uniform bounds for \(\int_0^H[(v+1/2)^{-1}+c/\sqrt{t_e}]^j dv\) are
\[
 I_3=2+6d_e+3d_e^2U+c^3e^{(1-3\nu)U/2},\qquad
 I_4=8/3+8d_e+12d_e^2+4d_e^3U+c^4e^{(1-4\nu)U/2}.
\]
Integrate the binomial expansions, use \(\log(1+2\sqrt T)\le\log T\), and note the decay of all frozen terms. The two vertical endpoints cost at most \(C(1+e^{(\nu-1)U})I_4\).

At an interior jump \(X=n\) of one polynomial, the difference of its two adjacent squares is at most \(2\tau_j(n)S_{j,v}(n)/\sqrt n\) after the phase normalization. A simultaneous jump is split by telescoping the two factors and using the larger endpoints. The other polynomial contributes the square of its full sum. For a forward jump, the two length factors yield \(y=(be^{-u}/(ae^u))n\). Partial summation by layer-cake gives \(\sum_{n\le X}\tau_j(n)n\le m_jX^2/2+D_jX\). After division by \(QT\) the total of both types of jumps is at most
\[
 \frac{I_3}{2\pi}\sum_{j\in\{f,d\}}
       (m_j+2D_jl_j^{-1}e^{-U/2}) M_j M_{\mathrm{other}}^2 .
\]
Together these terms give **harmonic(U,...)**, an absolute upper bound on the mixed harmonic divided by \(T\).

Finally let \(c_f,c_d\) bound the individual fourth norms divided by \(T\log^4T\), and \(h\) bound the mixed fourth harmonic divided by the same factor. Use
\[
 |A+e^{-i\phi}\overline B|^2=|A|^2+|B|^2+2\Re(e^{i\phi}AB).
\]
The \(L^2\) triangle inequality, followed by Cauchy–Schwarz for \(\int|AB|^2\), gives a normalized fourth root at most
\[
 \left[\sqrt{c_f}+\sqrt{c_d}
      +\sqrt{2(\sqrt{c_fc_d}+h)}\right]^{1/2}.
\]
This argument is applied on the product space including \(u\); the contour bound applies before averaging over \(u\). Add the disjoint early-time and AFE remainder by Minkowski as in the sharp proof. Running **python -B shifted_harmonic.py** gives respective uniform fourth constants below \(0.002624828,\ 0.001396509,\ 0.001276579\) at \(U=40,\alpha=1.25,w=.06,Z=384\) for \(Q=6,30,210\).

## Disjoint time ranges

The optional **disjoint_fourth** entry point uses the same paired contour and changes the last combination. Put \(e_{\rm AFE}=K(\log T/T)^{1/4}/\log T\), using the smooth \(K\) above, and let \(B\) be the normalized fourth root for the two main polynomials on \([t_0,T]\). The complete fourth-moment coefficient is at most
\[
 \frac{\sup|E_Q|^4[200(14)^4+(t_0-200)S_0^4]}{T\log^4 T}
       +(B+e_{\rm AFE})^4 ,
\]
where \(S_0=17\) for \(t_0=1000\) and \(S_0=4(t_0/(2\pi))^{1/4}+1\) otherwise. Indeed the first integral covers \([0,t_0]\); the second covers \([t_0,T]\) and the AFE remainder occurs only in it. For \(0\le t\le2\pi\), first-order Euler summation gives \(|\zeta(1/2+it)|\le1+2|1/2+it|<14\). For \(2\pi\le t\le200\), use the symmetric case of Simonič's Theorem 4, Table 1. Its bound \(4\sqrt y+4.257/\sqrt y\), \(y=\sqrt{t/(2\pi)}\), is below 12 at both endpoints and has an interior minimum. Each scalar cost decreases after freezing \(\log T=U\). At \(U=40,\alpha=1.25,w=.06,Z=384\) this gives \(0.002428783,\ 0.001226079,\ 0.001066792\) as upper fourth-moment coefficients for \(Q=6,30,210\), respectively.
