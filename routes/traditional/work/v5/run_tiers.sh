python -B scan5.py 66 80 "ROWS=inputs/bel_faithful_v1.csv" ROWS_KEEP_ORIG=0 TAG=v4repaired_bty
python -B scan5.py 70 86 "ROWS=inputs/bel_faithful_v1.csv" ROWS_KEEP_ORIG=0 Z1=5.558691 ROWS_STATUS=refereed TAG=v4repaired_pub
python -B scan5.py 45 80 "ROWS=inputs/bel_faithful_v1.csv;inputs/bel_reopt_v1.csv;inputs/bel_reopt_lam1_v1.csv" ROWS_KEEP_ORIG=0 Z1=5.558691 ROWS_STATUS=refereed TAG=ref+belfix
python -B scan5.py 45 80 "ROWS=inputs/bel_faithful_v1.csv;inputs/bel_reopt_v1.csv;inputs/bel_reopt_lam1_v1.csv" ROWS_KEEP_ORIG=0 Z1=5.558691 ROWS_STATUS=refereed BANDS=inputs/zfr_local_v1.csv TAG=ref+belfix+LW
python -B scan5.py 45 80 "ROWS=inputs/bel_faithful_v1.csv;inputs/bel_reopt_v1.csv;inputs/bel_reopt_lam1_v1.csv" ROWS_KEEP_ORIG=0 BANDS=inputs/zfr_local_v1.csv TAG=bty+belfix+LW
python -B scan5.py 40 80 "ROWS=inputs/bel_faithful_v1.csv;inputs/bel_reopt_v1.csv;inputs/bel_reopt_lam1_v1.csv" ROWS_KEEP_ORIG=0 Z1=5.558691 ROWS_STATUS=refereed BANDS=inputs/zfr_local_v1.csv CS=1 TAG=ref+belfix+LW+CS
python -B scan5.py 40 80 "ROWS=inputs/bel_faithful_v1.csv;inputs/bel_reopt_v1.csv;inputs/bel_reopt_lam1_v1.csv" ROWS_KEEP_ORIG=0 BANDS=inputs/zfr_local_v1.csv CS=1 TAG=bty+belfix+LW+CS
