# 复算说明

已运行环境：Python 3.12，NumPy 2.5.4，SciPy 1.18.1，python-flint 0.9.0。依赖列于`code/requirements.txt`。路径不依赖当前工作目录；以下示例假定位于本目录。

## k=6完整条件性证明的统一核验

```powershell
python -X utf8 code/verify_k6.py
```

该入口重放k6下端、k6新中段、旧k4实变量中远段及无限尾部四个主证书，检查闭区间拼接与区间包含关系，输出`ALL_K6_MODULES_VERIFIED`，并保存`results/k6_verification_summary.json`。全部正整数覆盖的解析论证见[六次幂完整证明](research/K6_PROOF.md)。这是接受QRH及列明文献输入后的证明模块核验，不是形式化内核验证。

单独只读检查新增模块：

```powershell
python -X utf8 code/certify_lower_range_k6.py --verify
python -X utf8 code/certify_smooth_k6.py --verify
```

新中段采用160-bit Arb、76个闭区间；独立实现的高精度复算见`code/review_smooth_k6.py`及`research/SMOOTH_K6_REVIEW.md`。新结果没有改写旧k4证书。

## 只读检查已有认证结果

统一入口会依次只读复核四个主证书，并写一份汇总；它会明确保留尚未覆盖区间，不会输出全范围k4已证明。新增375–400段的全量复算约需两分钟，全部检查耗时随机器负载变化：

```powershell
python -X utf8 code/verify_all.py
```

```powershell
python -X utf8 code/certify_lower_range.py --verify
python -X utf8 code/certify_smooth_extension.py --verify
python -X utf8 code/certify_tail_cs.py --verify
python -X utf8 code/certify_smooth_segment.py --verify
```

主结果使用CSv2密度输入。`certify_tail.py`保留的是较早的FKS尾部模块，不属于当前主证明链的必要输入。

## 探索实验

```powershell
python -X utf8 code/smooth_scan.py --check-only
python -X utf8 code/smooth_scan.py --density cs2 --output smooth_all_k_cs2
python -X utf8 code/smooth_scan.py --ks 4 --density cs2 --ls 100,105,109.46,110,115,120,130,150,200,250,300,350,375,400,425,450,460,470,500,600,700 --output smooth_k4_cs2
python -X utf8 code/smooth_scan.py --ks 4 --degrees 2,3,4,6,8,12,16,24,32 --density cs2 --ls 105,109.46,110,115,120,130,150 --output kernel_order_study_cs2
python -X utf8 code/smooth_scan.py --ks 3 --density cs2 --ls 1000,1250,1500,1600,1700,1800,2000,2200,2500 --output smooth_k3_extended_cs2
python -X utf8 code/sharp_scan.py --ks 4 --output sharp_k4
```

最后一条锐截断对照仍使用CSv1，文件manifest注明来源，不能与v2数据混称同一输入版本。`--no-bv`与`--no-symmetry`用于单项对照实验。

探索CSV和JSON中全部标记`EXPLORATORY`。JSON记录参数、代码SHA256、CSV SHA256及限制；新扫描同时保存对应代码快照。早期v1产物仅作历史记录，相关版本变化记入日志。

数值稳定性检查不等于区间认证；不应把CSV中相邻两个通过点间的区域自动计入证明。

## 结果文件

- `lower_range_certificate.json`：完整44721个素数见证及CHL整数覆盖。
- `tail_cs_certificate.json`：无限尾部的数值前提；无限范围依赖解析单调证明。
- `smooth_segment_certificate.json`：有限中远段的逐闭区间Arb上界。
- `smooth_extension_certificate.json`：第二轮新增的375–400段，32个连续闭单元。
- `verification_summary.json`：四个主证书的统一重放记录、文件散列及保守未覆盖区间；首轮汇总另保存在`verification_summary_round1.json`。
- `smooth_*cs2.csv`：当前密度输入的浮点筛选；没有全范围证明效力。
- `kernel_order_study_cs2.csv`：平滑阶数最高32的对照，保留失败。

## 第二轮诊断与探索

```powershell
python -X utf8 code/midrange_budget.py
python -X utf8 code/density_envelope_round2.py
python -X utf8 code/mellin_envelope_round2.py
python -X utf8 code/signed_kernel_round2.py
python -X utf8 code/structural_round2.py --verify
```

前四条重建浮点探索结果。有符号核实验完整保留有限LP、候选重算与强制负权控制例；频率采样不具有连续上确界认证效力。最后一条只读重放抽象模型构造的有限Arb条件；其连续范围仍依赖文字证明。模型诊断不是素数区间认证，不并入`verify_all.py`的覆盖链。更强β上限和更高有限RH高度的敏感性实验均是明确反事实，不是新增的工作假设。
