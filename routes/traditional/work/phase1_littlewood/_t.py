import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_profile as CP, time
t=time.time()
CP.GT.check_increasing(); print('G increasing verified', round(time.time()-t,1))
for v in [30, 31, 32, 40, 47, 56, 80, 129, 130, 200, 296, 299]:
    print(v, CP.z_local(v), flush=True)
