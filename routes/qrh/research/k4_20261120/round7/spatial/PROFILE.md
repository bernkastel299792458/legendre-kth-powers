# A compact physical weight for the fourth-power upper interval

**Connected suffix beginning at \(L=143.874\).** On each sixteenth-unit log-height slab the two valid fourth-moment enclosures from [the endpoint sweep](../../round8/critical/SWEEP_TABLE.md) and [the balanced Euler factors](../../round8/critical/BALANCED.md) apply to the same critical norm. Take their minimum on that slab. Above log height 46 use ten unit slabs through 56, and beyond it the minimum of the two independently uniform half-line estimates. Taking suffix maxima across these intervals gives a constant valid at every later height in each application of the critical norm. Each local cap and each left and right boundary constant is rounded upwards to a multiple of \(10^{-20}\). Use both core lengths, the [second prime coordinate](../taper/JORDAN.md), and the same angular detector. The complete scan of \([142.90,144.12]\) has a maximum above 1.0294. Its consecutive accepted cells from the right contain \([143.874,144.12]\) with total cost below .999948. The overlap with the following certificate starts at 144.009. This covers each integer \(n\ge4\,177\,544\,380\,332\,689\), conditionally on the stated inputs.

~~~powershell
python -B round7/spatial/parallel_profile.py --first 142.90 --last 144.12 --join 143.874 --sub 16 --nh 28 --mesh 192 --cutoff 320 --workers 6
~~~

**Connected suffix beginning at \(L=144.009\).** In \([143.55,145.18]\) use the positive polygon below, the [moving-endpoint fourth-moment table](../../round8/critical/SWEEP_TABLE.md), a frequency cutoff of 300 (or the end of the valid taper range if smaller), and the adaptive core. Test every physical cell of length at most \(1/192\), every eighth-unit slab of log height with 48 samples, and all real-part knots. Starting at the right and retaining consecutive cells with complete cost \(<1\) gives a suffix containing \([144.009,145.18]\); the maximum certified cost on the retained suffix is below .999975. The full scan's maximum near the left edge exceeds 1.0139. Rounding the suffix start upwards and joining to the covered half-line gives every \(n\ge4\,320\,942\,739\,090\,268\) under the stated assumptions.

~~~powershell
python -B round7/spatial/height_profile.py --first 143.55 --last 145.18 --join 144.009 --cutoff 300 --nh 48 --mesh 192 --sub 8 --rough --sweep-table --adapt-core --prime --real --tight
~~~

For every \(146.30\le\log x\le146.401\) the normalized explicit-formula upper cost is below **.999194**. The real-variable Mellin interval beginning at 146.4 overlaps this interval. With the same QRH(7/8), validated zero heights and analytic inputs as the preceding bridge, every \(n\ge 7\,661\,621\,190\,973\,252\) therefore has a prime strictly between the consecutive fourth powers. [Preceding bridge and inputs](../taper/CAUSAL.md)

Use the 33 fixed integers \(H_0,\dots,H_{32}\) in the replay. Put \(h=1/64,\ S=H_0+2\sum_{j=1}^{32}H_j\). On \([0,1]\) interpolate the heights \(H_j/(hS)\) at \(1/2\pm jh\), and use zero outside. The resulting density has mass one, vanishes at the two endpoints and has maximum at most \(3/2\), since \(128\max H_j\le3S\). For ordinates with \(y=\gamma\log(1+4x^{-1/4})\) use the decreasing majorant of the damped Fourier modulus from the [polygonal interpolation proof](../../round5/kernel/PROOF.md), recalculated with these integers. In particular the variation at both external tips is included. The code encloses the Chebyshev numerator at every endpoint of a frequency cell of width \(1/256\), applies the second-derivative interpolation bounds to both the transform and its numerator, and takes the smaller with the global variation divided by \(y^2\). The undamped estimates gain \(d/2,\ d=\log(1+4e^{-146.30/4})\), to enclose every actual damping. At \(y\ge192\) the inverse-square tail applies without truncation. The [prime-power bound](../../round2/spectrum/PROOF.md) is linear in the maximum of the density. The replay adds one eighth of the previous \(4/3\) charge as \((3/2)/(4/3)=9/8\), bounding this extra charge using the extreme enclosing physical endpoints.

The detector, modulus 2310 on both boundaries, centered critical fourth moment, real-variable Mellin energy, 128 original local cells, finite-height verification, negative ordinates and infinite tail follow the [Mellin bridge](../taper/MELLIN.md) and its [real-variable refinement](../taper/CAUSAL.md). With 128 height samples per half-unit and physical mesh \(1/192\), the full result was \(0.999193028\) to the displayed precision. Using the preceding physical weight with exactly that same mesh and detector gives a computed upper budget above 1.000251. These upper budgets measure the two methods on the specified closed interval.

~~~sh
python -B round7/spatial/height_profile.py --first 146.30 --last 146.401 --nh 128 --mesh 192 --real
~~~

## Eighth-unit height slabs

The same fixed polygon and detector now cover \(146.18\le L\le146.301\) with full budget below **.999773**. The interval overlaps the preceding one at 146.30. Thus the conditional upper half-line includes every \(n\ge7\,435\,186\,064\,520\,594\). Subdivide each unit of log height into eight closed intervals and take 32 height samples in each one; use a physical mesh of \(1/192\). For each real-part knot \(s\), the actual high-ordinate hinge sum \(\sum_{H<\gamma\le T}(\beta-s)_+\) is nondecreasing in \(T\), so the minimum of all subsequent certified upper bounds at that same \(s\) remains an upper bound. Apply these suffix minima before any physical weights. The lower-height part and infinite tail use the same estimates as above. On the intermediate trial \([145.95,146.301]\) the computed upper budget was above 1.0074 using 24 samples per eighth and mesh \(1/128\).

~~~sh
python -B round7/spatial/height_profile.py --first 146.18 --last 146.301 --nh 32 --mesh 192 --real --tight --sub 8
~~~

## Residue Gram cutoff and arithmetic variance

Keeping the same polygon, include all frequency cells through 160 in the [outer residue Gram estimate](../../round5/mean/RIGHT.md). The original tail majorant begins at the increased cutoff. This proves the full budget is below .998919 on \([146,146.181]\). In the same right-hand norm, the [conditional Jordan variance](../taper/JORDAN.md) subtracts a nonnegative quantity for true Möbius coefficients at primes 13 through 97. The full budget on \([145.94,146.181]\) is then below **.999467**. The slab overlaps at 146.18, giving \(n\ge7\,002\,194\,536\,165\,343\). All intervals are closed.

~~~sh
python -B round7/spatial/height_profile.py --first 146 --last 146.181 --nh 32 --mesh 192 --real --tight --sub 8 --cutoff 160
python -B round7/spatial/height_profile.py --first 145.94 --last 146.181 --nh 48 --mesh 192 --real --tight --sub 8 --cutoff 160 --jordan
~~~

## Moving endpoints of the fourth moment and the right-hand variance

The [rational critical fourth moment](../../round8/critical/RATIONAL.md) and the prime-coefficient improvement in the right mean give a normalized budget below .999228 on \([145.62,145.945]\). For the next slab count smaller integers and the additional disjoint radicals in [the Jordan variance](../taper/JORDAN.md), use the [endpoint Hilbert estimate](../../round8/critical/ENDPOINT.md), and optimize the length of the auxiliary core in the critical norm at its actual height. For the latter take the smaller complete left norm between the original length \(2^{20}\) and \(2^{\max(12,\min(20,16+\lfloor2(U-34)/3\rfloor))}\). The detector polynomial itself and the right-hand boundary are fixed. The resulting cost is below .997794 on \([145.16,145.625]\); both successive joins overlap.

~~~powershell
python -B round7/spatial/height_profile.py --first 145.62 --last 145.945 --nh 48 --mesh 192 --real --tight --sub 8 --cutoff 280 --jordan --rational --prime
python -B round7/spatial/height_profile.py --first 145.16 --last 145.625 --nh 48 --mesh 192 --real --tight --sub 8 --cutoff 280 --rough --endpoint --adapt-core --prime
~~~

The modulus-210 weighted Hilbert endpoint gives the certified upper bound .991491 on \([145.00,145.625]\), extending the high half-line to every integer \(n\ge5\,535\,730\,883\,721\,925\). The positive mixture of the residue-class quadratic forms and the finite spectral bound are derived in [the endpoint estimate](../../round8/critical/ENDPOINT.md).

~~~powershell
python -B round7/spatial/height_profile.py --first 145.00 --last 145.625 --nh 48 --mesh 192 --real --tight --sub 8 --cutoff 290 --rough --weighted --adapt-core --prime
~~~
