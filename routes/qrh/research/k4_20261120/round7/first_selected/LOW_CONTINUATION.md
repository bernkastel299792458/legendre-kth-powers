# Low-end continuation using the frozen sixth-round certificate

Starting at the [sixth-round endpoint \(115.040500\)](../../round6/first_rect/LOW_JOIN.md), keep the same sieve addition \(1.16613\) and the same finite-RH and QRH(7/8) assumptions. Use the existing [local hinge verifier](../../round6/first_rect/low_replay.py) and its [transfer proof](../../round6/first_rect/LOW_JOIN.md). With reference endpoints \(l_0=115.040500, h_0=115.041000,\ K-H=16000000000\), take 96 equal height cells and \((\delta,W,\log h)=(.73,7.8,-2.65)\). The finite high-zero charge is below \(0.005937108818\). The complete reference budget exceeds one by less than \(2.05\cdot10^{-7}\).

Reevaluate the physical, verified-zero, and remote terms at each pair of actual endpoints. With the transfer ratio of the earlier proof the following three full costs have strict upper bounds.

| Closed \(L\) interval | Complete normalized cost |
|---|---:|
| \([115.040500,115.040900]\) | \(0.999960228287\) |
| \([115.040900,115.041000]\) | \(0.999999130811\) |
| \([115.041000,115.041002]\) | \(0.999999667199\) |

These three slabs join the previous endpoint and give continuous conditional coverage through \(115.041002\). The reference charge and transfers can be replayed from the directory containing the round folders.

~~~powershell
python -B round6/first_rect/low_replay.py --lo 115.040500 --hi 115.041000 --size 16000000000 --panels 96 --mesh 1 --case .73,7.8,-2.65 --check-high .005937108818
python -B round6/first_rect/low_join.py --reference-lo 115.040500 --reference-hi 115.041000 --size 16000000000 --high .005937108818 --lo 115.040500 --hi 115.040900 --check
python -B round6/first_rect/low_join.py --reference-lo 115.040500 --reference-hi 115.041000 --size 16000000000 --high .005937108818 --lo 115.040900 --hi 115.041000 --check
python -B round6/first_rect/low_join.py --reference-lo 115.040500 --reference-hi 115.041000 --size 16000000000 --high .005937108818 --lo 115.041000 --hi 115.041002 --check
~~~
