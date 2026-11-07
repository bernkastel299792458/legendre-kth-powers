"""Referee: reproduce Lemma-A row-1 value and test sensitivity to the RZA error term (x10)."""
import sys, math
sys.path.insert(0, r"D:\UGit\AI4Math\legendre_k67\work\phase2_lemmas")
import lemmaA_d4 as A
from flint import arb
u, v, x = "2.1781287", "4.4744028", "7.0798370"
La, Lb = math.log(3e12), 29.0
b, det = A.d4_upper(u, v, x, La, Lb)
print("reproduced row-1 d4 bound:", A.f_up(b), det)
orig = A.M1Data.rbar
def rbar10(self, ly): return 10 * orig(self, ly)
A.M1Data.rbar = rbar10
b10, det10 = A.d4_upper(u, v, x, La, Lb)
print("with RZA error x10:", A.f_up(b10), " ratio", A.f_up(b10) / A.f_up(b))
