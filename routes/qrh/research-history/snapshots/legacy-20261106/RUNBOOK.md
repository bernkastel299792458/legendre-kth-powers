# 复算说明

已运行环境：Python 3.12，NumPy 2.5.4，SciPy 1.18.1，python-flint 0.9.0。依赖列于`code/requirements.txt`。路径不依赖当前工作目录；以下示例假定位于本目录。

## k=6完整条件性证明的统一核验

```powershell
python -X utf8 code/verify_k6.py
```

该入口重放k6下端、k6新中段、旧k4实变量中远段及无限尾部四个主证书，检查闭区间拼接、区间包含关系及固定公式下CS三列常数统一乘以53/50的容差，输出`ALL_K6_MODULES_VERIFIED`。默认会写入`results/k6_verification_summary.json`；子模块的`--verify`只读。完全不写汇总或另存汇总可分别使用：

```powershell
python -X utf8 code/verify_k6.py --dry-run
python -X utf8 code/verify_k6.py --output results/k6_verification_custom.json
```

两个选项互斥。全部正整数覆盖的解析论证见[自洽稿件](manuscript/K6_conditional_primes.md)及[证明入口](research/K6_PROOF.md)。这项核验显式接受H1：QRH(7/8)、H2：CS arXiv:2507.15184v2推论1及所用表1常数，以及列明辅助输入；CS按预印本处理。本工具不是形式化内核验证。

单独只读检查新增模块：

```powershell
python -X utf8 code/certify_lower_range_k6.py --verify
python -X utf8 code/certify_smooth_k6.py --verify
```

当前中段采用256-bit Arb、94个闭区间，σ网格步长1/4096、高度对数网格步长1/64，最坏δ≤0.939735996783828324763044。独立512-bit复算与全部94格保存的仿射分解检查使用：

```powershell
python -X utf8 code/review_smooth_k6_refined.py
```

见[精化说明](research/K6_REFINED_CERTIFICATE.md)及[新数值审阅](review/K6_revision_numeric_audit_2026-11-06.md)。原160-bit、76格版本完整保存在`archive/k6_before_claude_revision_2026-11-06/`，附SHA256清单。`code/review_smooth_k6.py`现在默认读取归档旧证书，只供历史重放；它不能用于核验新94格版本。原k4证书未改写。

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

## k4第三轮复算入口（2026-11-06）

当前统一入口仍为 `python -B -X utf8 code/verify_all.py`。
它重放七个模块，核对带限段与旧下端、单调无穷段与冗余有限段的精确衔接，
然后写入 `results/verification_summary.json`。预期状态仍是
`PARTIAL_MODULES_VERIFIED_NOT_FULL_K4`，保守缺口为 `225/2 < log(x) < 372`。

新增模块的只读重放：

```powershell
python -B -X utf8 code/k4_bandlimited_round3.py --verify
python -B -X utf8 code/certify_k4_round3.py --verify
python -B -X utf8 code/certify_k4_monotone_round3.py --verify
python -B -X utf8 code/audit_k4_round3.py --verify
```

- 带限段用19项有限检查支撑文字证明：其中16项属于新覆盖，3项仅属L120模型诊断。
  不能把模型诊断当成素数证书，也不能把普通球计算称为整篇公式形式化。
- 梯形段20格完整重放约4秒；单调尾另重算一点预算与全部正衰减率。
  覆盖无穷所需的解析比较在 `research/K4_MONOTONE_ROUND3.md`。
- `audit_k4_round3.py` 不导入认证函数，以512位另算点372与最坏格；它不是全部20格的分离实现。
- 新脚本不修改k6或旧证书。非`--verify`入口会重新写本脚本专属JSON，核对或审阅时优先使用只读入口。
- 第二轮汇总保留为 `results/verification_summary_round2.json`。

## k4第四轮复算入口与分支（2026-11-06）

当前统一入口 `python -B -X utf8 code/verify_all.py` 已加入 Selberg 新段，共八个模块。
新段单独只读验证：

```powershell
python -B -X utf8 code/k4_selberg_round4.py --verify
```

它重算19项严格比较，核对固定源、参数、代码与文字证明散列；实际解析连接见
`research/K4_SELBERG_ROUND4.md`。新段15项标量前提及4项整数端点覆盖整段
`225/2≤log(x)≤1131/10`，不是点采样。预期统一汇总为保守缺口
`1131/10 < log(x) < 372`，`full_k4_proved=false`。

第三轮统一汇总另存`results/verification_summary_round3.json`。
用户侧计算算法分支独占`computation_branch/`，其命令与数据以该分支自身文档为准；
主验证器没有把它的实验性素数搜索自动纳入证明覆盖。

## k4第五轮理论复算（2026-11-06）

从本目录执行：

```powershell
python -B -X utf8 theory_round5/rebase_density.py --verify
python -B -X utf8 code/verify_all.py
```

第一条只读复算高高度CS常数、L362一点预算、全部连续衰减率及散列。
第二条重放九个正式模块并写统一汇总，理论缺口为`1131/10<log(x)<362`。
新结果前提见 `theory_round5/PROOF.md`，其中CS Theorem 1/Corollary 5及有限RH不可省略。
第四轮汇总原样保存在 `results/verification_summary_round4.json`。
`theory_round5/lower/` 和 `upper/` 的新候选按各自状态阅读，不自动计入主链。

