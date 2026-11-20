# Physical intervals obtained with rotating scalar sources

Write \(L=4\log n\) and assume the project QRH(7/8), finite-height RH and the inherited explicit moment and edge estimates in the [Green proof](../../round8/zero_strip/COMPLETE_GREEN.md). The complete normalized cost must be strictly less than one on each closed interval.

The [signed circle inequality](../../round8/zero_strip/ROTATING_SIGNED.md) applies to the scalar real-part hinges, with nine eighths of the archived horizontal allowance for a degree-nine determinant. Populate the earliest four log-height units by all seven actual mollifiers using the [early source calculator](../../round8/zero_strip/early_green_rows.py). When a real-part source is convexified up to the terminal abscissa \(7/8\), the zero hinge at that abscissa uses QRH. The ordinate tail uses the independent global fourth-moment formula. This gives a complete upper bound below **.865878** on 40 closed cells covering \([125,135]\). The upper endpoint joins the separate nine-cell positive-circle bridge through 137.25, whose maximum was below .743761 after including the degree-nine allowance.

On 28 closed cells covering \([121.5,125]\), the complete upper bound is below **.968445**. These ranges use the fixed compact polygon and its true Fourier envelope. The [scalar bridge](../../round8/zero_strip/rotating_bridge.py) recomputes the low verified zeros, the zero-density contribution, the last analytic tail, the damping allowance, prime powers and trivial zeros.

~~~powershell
python -Bu round8/zero_strip/early_green_rows.py --destination round8/zero_strip/early_green_rows.json
python -Bu round8/zero_strip/rotating_bridge.py --first 125 --last 135 --pieces 40 --low 29 --high 41 --sub 8 --nh 2 --step 8 --table round8/zero_strip/early_green_rows.json
python -Bu round8/zero_strip/rotating_bridge.py --first 121.5 --last 125 --pieces 28 --low 29 --high 41 --sub 8 --nh 2 --step 8 --table round8/zero_strip/early_green_rows.json
~~~

The [height allocation](HEIGHT_ALLOCATION.md) also allows a different compact polygon, separate positive and negative spectral envelopes, and additional true cumulative heights from the translated rectangles near the verified height. Using the positive- and absolute-cosine allocations gives a full upper bound below **.933823 on \([115.425,115.45]\)**. The identical grid at \([116,116.025]\) gave 1.007781, and at \([118,118.025]\) it gave 1.071979. Each number is a full upper bound for its physical cell. A value above one does not decide the prime assertion there.

~~~powershell
python -Bu round7/spatial/height_allocation.py --lo 115.425 --hi 115.45 --source round8/zero_strip/early_green_rows.json --rotate --verified-start --design 28 --signed-limit 60 --nh 2 --sub 8 --step 6 --near-rows 'round7/first_selected/companion_original_100.json,round7/first_selected/companion_original_350.json,round7/first_selected/companion_rows_600.json' --check
~~~
