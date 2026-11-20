# Regenerating the near-height inputs for the fourth-power certificate

Run the following from the research directory containing this file. The two generators run in separate Python processes. Each signed companion uses the freshly regenerated scalar file in the temporary directory. A successful run compares the actual bytes with the archived files and prints the byte count and SHA-256 digest of each copy.

~~~powershell
@'
from hashlib import sha256
from pathlib import Path
from subprocess import run
from sys import executable
from tempfile import mkdtemp

source = Path("round7/first_selected")
out = Path(mkdtemp(prefix="qrh-k4-near-cold-"))
print("Generated files in", out, flush=True)

def generate(script, *args):
    run([executable, "-Bu", source / script, *map(str, args)], check=True)

def compare(name):
    archived = (source / name).read_bytes()
    generated = (out / name).read_bytes()
    assert generated == archived, name
    print(name, len(generated), sha256(generated).hexdigest(), flush=True)

for label, panels in [(100, 10), (350, 12), (600, 12)]:
    name = f"companion_rows_{label}.json"
    generate("companion_heights.py", "--size", label * 10**9, "--panels", panels,
             "--location", "115.402", "--table", out / name)
    compare(name)

for label in [100, 350]:
    name = f"companion_original_{label}.json"
    generate("companion_phases.py", "--original", "--lo", "115.400",
             "--hi", "115.455", "--scalar", out / f"companion_rows_{label}.json",
             "--table", out / name)
    compare(name)
'@ | python -Bu -
if ($LASTEXITCODE -ne 0) { throw "Near-height input regeneration failed" }
~~~

For the panel ending at index \(j\) out of \(m\), the tables store a cumulative bound through \(H+\lceil(S+1\,280\,000)j/m\rceil\), with \(H=3\,000\,175\,332\,800\). Both generators use 192-bit Arb arithmetic and round upward to integer multiples of \(10^{-15}\). The archived scalar rows are evaluated at \(L=115.402\). The extra signed rows cover \(115.400\le L\le115.455\). The height allocator checks that this domain contains its whole physical cell before using the signed entry. The signed files contain their parent scalar entries as well. The rotating bridge reads the two signed files and the scalar file for \(S=600\,000\,000\,000\). [Scalar generator](round7/first_selected/companion_heights.py), [signed generator](round7/first_selected/companion_phases.py), [height allocator](round7/spatial/height_allocation.py), [bridge inputs](round8/zero_strip/ROTATING_HARMONICS.md).

The additive 1,280,000 in the ordinate is the Gaussian padding \(128Q\) for \(Q=10^4\). The nominal cutoff is \(K=H+S\) and the last panel reaches \(K+128Q\). In the original signed calculation for the panel through \(H+D\), the test is frozen on \([H,H+D+1]\). Its lower horizontal edge is chosen at a cosine extremum in \((H,H+0.1)\). The omitted part of the positive-ordinate sum is charged at most \(e^{-115.400/8}B(0.1)<0.000008179924\), using QRH and the cumulative zero-count bound

\[
B(v)=0.3\log H+6+\left(\frac{\log(H/(2\pi))}{2\pi}+\frac{0.15}{H}\right)v+\frac{v^2}{4\pi H}.
\]

The cutoff for trying that signed bound is \(\log(D/2)>20\). Its full translated moment uses radius \((D+1)/2\). For smaller panels the signed generator retains the transferred scalar bound. [Near-height cutoff](round4/low/NEAR_HEIGHT.md), [translated horizontal edges](round7/spatial/PHYSICAL_PHASE.md), [zero-count increment](round5/low/SHORT_BOX.md), [implemented bound](round7/first_selected/near_phase.py).

All five generator invocations exited successfully. A final direct binary comparison matched every temporary file with its archived counterpart, including both signed derivatives of freshly regenerated inputs.

| File | Bytes | SHA-256 of both copies |
|---|---:|---|
| companion_rows_100.json | 248 | fc956ccc512ab02c4d7202b702cbe9df0258e2a29d8fd94b8d1f7d7108b7d70b |
| companion_rows_350.json | 287 | 75536551fd93388d63ecede612ef0ad90f3703d72cd97f64d3dc7b0ccfba332b |
| companion_rows_600.json | 290 | 51dfe6886b4402048b6ad1b2f16bffd91911c4c8d44ee29964f9fea24539acc2 |
| companion_original_100.json | 468 | 7f9d57d0dba75bc66c377c33b37885f8bb4d2fea9712ede14cd242c61868dd35 |
| companion_original_350.json | 539 | 95af62f93705c1795c34cfab16ad0b2f6402a2b6ca0e04244cd7af17e07bcd49 |

## Base table

The original 208-slab table was rebuilt separately from its two fourth-moment families. A half-line cap beginning at log height 56 and ten unit intervals above log height 46 initialize the backward maximum. All 208 resulting integer caps matched. Six disjoint residue classes of the indices 528 through 735 then reproduced 2,912 boundary moments, 2,688 displaced moments and 1,456 horizontal edge charges. Each class contributed 1,176 integer checks. Reassembly reproduced all 170,889 bytes of the input. Its SHA-256 is `de2c0f8df20626776190ffc61aeee56c1ef365bdabb70adea64cca0089f097e8`. The original generator and its complete command are documented in the [moving-line proof](round8/critical/MOVING_LINE.md).

## Single-process displacement extension

The displacement generator runs the row function directly when called with \(\texttt{--workers 1}\). The default remains four worker processes. The extension reads the archival 16-step height table and evaluates three new displacements for each of seven mollifier parameter triples in 128 slabs. Its source contains 208 total slabs. The other 80 slabs are carried forward. The early-height generator uses the extended table in the separate regeneration of the early spectrum. [Displacement generator](round8/zero_strip/phase_shift_extra.py), [source-table construction](round8/critical/MOVING_LINE.md), [early-height construction](round7/spatial/ROTATING_JOIN.md).

~~~powershell
@'
from hashlib import sha256
from pathlib import Path
from subprocess import run
from sys import executable
from tempfile import mkdtemp

source = Path("round8/critical/shift_rows_16.json")
destination = Path(mkdtemp(prefix="qrh-k4-displacements-")) / "phase_shift_extra.json"
archive = Path("round8/zero_strip/phase_shift_extra.json")
assert sha256(source.read_bytes()).hexdigest() == "de2c0f8df20626776190ffc61aeee56c1ef365bdabb70adea64cca0089f097e8"
run([executable, "-Bu", "round8/zero_strip/phase_shift_extra.py", "--workers", "1",
     "--steps", ".016,.020,.026", "--source", source, "--destination", destination],
    check=True)
generated = destination.read_bytes()
assert generated == archive.read_bytes()
print(destination, len(generated), sha256(generated).hexdigest())
'@ | python -Bu -
if ($LASTEXITCODE -ne 0) { throw "Displacement input regeneration failed" }
~~~

The full single-process regeneration matched all 227,358 archived bytes, with SHA-256 fda6719c59efa3aa087e774578d5197f5eca8e4c70cae9855df72f50037e8cda. A separate regression ran the first two extended slabs, indexed 544 and 545, with one and two workers. Both outputs matched the same two slabs from the archived extension after retaining the metadata and compact JSON serialization. Each output was 3,112 bytes with SHA-256 f802ee85a0303aa653dae2c3cffe5984b8425204f170fcc07cd01e58694294f5.

In a separate frozen checkout, the coordinating run regenerated all eight early half-unit slabs. The early generator exited successfully after comparing the entire parsed JSON object with the archived table. The SHA-256 digest of the archived early_green_rows.json is 6cfc5297aad784ba7b112de2ee6804099dc0ef53c78a19c2b68ae7e8003a1a58. To replay this structural comparison with the destination already present, run the following command from the research directory.

~~~powershell
python -Bu round8/zero_strip/early_green_rows.py --source round8/zero_strip/phase_shift_extra.json --destination round8/zero_strip/early_green_rows.json
~~~

The reproduction environment used CPython 3.12.10, python-flint 0.9.0 with FLINT 3.6.0, NumPy 2.5.4 and SciPy 1.18.1.

2026-11-20. Joint project attribution to Claude and Codex.
