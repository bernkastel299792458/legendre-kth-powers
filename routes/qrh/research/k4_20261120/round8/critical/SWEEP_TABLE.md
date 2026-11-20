# A shared grid of fourth-moment half-lines

The [batch verifier](sweep_table.py) reuses the finite-slab inequality proved for [the two moving endpoints](SWEEP.md). Each grid index \(i\) corresponds to the lower endpoint \(i/d\), with \(d=8\) by default. Given a finite collection of Arb heights it rounds the **lower endpoint** of each input enclosure down to the grid. It computes one bound on each closed interval \([i/d,(i+1)/d]\) from the lowest requested index through the first integer strictly beyond the highest requested index. Above that integer, it computes ten adjacent unit slabs by default, followed by the complete previously proved [rational tail](RATIONAL.md) at the last right endpoint. The suffix maxima include that tail and every intervening interval. Thus an entry bounds all greater true heights, including when a requested height lies exactly on a grid boundary.

~~~python
from sweep_table import index, table
rows = table(heights, den=8)
coefficient = rows[index(U, 8)]
~~~

At quarter-unit resolution the independent replay gives coefficients below .000745947 at \(U=37\) and .000737110 at \(U=37.25\). Run with the same precision as the intended enclosing calculation.

~~~powershell
python -B round8/critical/sweep_table.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
