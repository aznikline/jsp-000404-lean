# Actual heavy clump 的原权重下界

日期：2026-10-08。初稿为 SOURCE_ONLY；后续按 Root 正式唯一 slot 完成 strict 与 genuine normal，三个公开结果均实际 PASS。未运行 Git。

新来源为 [ActualHeavyClumpWeight.lean](../Jsp000404/ActualHeavyClumpWeight.lean)。主生产器
$\texttt{exists\_actual\_heavy\_clump\_weight}$
只接受原 n4 LOW cap-16 minimal actual Model、原 score-two heavy $p$，以及在 $p$ 处一个实际夹角至少为 $2\lambda$ 的原 witness pair。

返回的 Data 包含内部产生的 actual maximal-low-row clumps、两个 Bool sides 各至少两点，以及两个 side 的原权重下界。没有 caller clump、window、restriction、gain、原 $F$ 数值或 deletion-budget 前提。

## 原实际几何与 companion

原 low-band floor 和 score-two defect 内部给出 $p$ 的原 fullHull 身份。已核的
$\texttt{ActualMaximalLowRowClumps.exists\_actual\_maximal\_low\_row\_clumps}$
给出两个非空原实际 clumps，总宽至多

\[
R=\pi-4\lambda<\lambda/2,
\]

异 clump 实际角至少为 $2\lambda$。

原 heavy observer 的每个单删 gain 都为零。若某 target 没有同 clump companion，所有另外的射线都与它异 clump，实际角至少 $2\lambda\ge\lambda$，已有 actual emission 定理给 gain 至少一，矛盾。因此两端各至少两点，不要求这些 targets 都是 light。

## 删除整端、保留真实另一端

固定一个内部产生的端 $C$，保留其补集 $S$。$S$ 包含原 heavy $p$ 和另一端至少两点，故 $|S|\ge3$；$C$ 非空使 $S$ 是原点集的 proper subset。

源码用 $S$ 的 Finset order-isomorphism 枚举一个真实 injective restriction，且证明其 image 恰为 $S$。因此 ledger 的 removedWeight 恰是整端 $C$ 的原权重，而不是只删了部分或额外点。

原 hull vertex $p$ 在该实际 restriction 仍是 hull vertex。来源通过原点不属于其他原点 convexHull，再用 image subset 与 convexHull monotonicity，推出受限点不属于受限 others 的 convexHull。这里只继承 hull extremality，不构造或继承 restricted minimal counter。

## 新实际 window 的宽度

对受限配置内部产生新的实际 hull Window。其真实 left/right endpoint indices 都不是 retained heavy，且映射回原配置后都在未删的同一个 Bool clump。

原 actual same-clump angle bound 给出这两条实际射线在原 heavy 处夹角至多为 $R$。再使用新 Window 的
$\texttt{width\_eq\_actual\_angle}$
得到新 Window 宽度至多为 $R$。

没有把 same-angle bound 无条件替换成 window width，也没有要求新旧 Window 的坐标或 boundary witness 相同。新宽度是通过新 Window 自己的两个真实端点计算的。

已核的
$\texttt{ActualHullWindowScoreLower.rowScore\_ge\_three\_of\_remainder\_window}$
于是给 retained heavy 的新 score 至少为 $3$。它原 score 为 $2$，原质量 $4$，新质量至少 $8$，所以该项 actual restriction expense 至少为 $4$。

## 只用原 proper-subset ledger

令原实际 potential 为 $F$。已核的原 Model ledger 给出

\[
\operatorname{expense}(S)+(F-16)\le W(C).
\]

因此，两个 Bool 端都满足

\[
\boxed{W(C)\ge(F-16)+4}.
\]

整个删除链只使用原 H 的 proper-subset cap；没有在中间点集套一次原 critical debt。

## 两个原支持 corollaries

* 原 $F=18$ 时，$W(C)\ge6$。若某端全部为原 score-one light，质量恰为 $2|C|$，故 $|C|\ge3$。公开生产器为 $\texttt{exists\_actual\_F18\_heavy\_clumps\_pure\_light\_card\_ge\_three}$。
* 原 $F=17$ 时，$W(C)\ge5$。若某端全部为原 score-zero targets，质量恰为 $|C|$，故 $|C|\ge5$。公开生产器为 $\texttt{exists\_actual\_F17\_heavy\_clumps\_pure\_zero\_card\_ge\_five}$。

F17 的支持条件仅是原 score-zero，允许原 hull 和原 interior 混合；没有使用已审出 vacuous 的“整个分离块全部原 interior”条件。

## 下一步消费者的短计划

本文件没有抢先写大消费者。对 unique-heavy F18、actual-wide heavy，两个端自动全部 light，所以各至少三点。Root 的后续短链可按以下顺序接入：

1. 若 heavy 在某原 interior light 的 apex，两个 nonapex 各至少两点，使 apex 除 heavy 外至多两点；三尺度三角传递把 interior center 与全部 nonapex 放到 heavy 的同端，另一端至多两点，矛盾。
2. 若另一个 interior 位于该点 apex，非apex 点和原中心在另一个 interior 的一类至少四点，且含 heavy；另外两纯 light 类各至少两点，超过八点配置每行七 targets。
3. 所以该 interior 的 apex 只有原 HullLight，PureLightBlock 给至少四点。它与 center 在 heavy 同端，至少五点，另一端至多两点，再次矛盾。
4. 没有 interior 时，使用已核 OneHeavyAllHull consumer。

这只是供后续实现的接口计划，未在此 note 声称整个 HM/HO unique-heavy 消费者已经 kernel 闭合。

## 核验范围

数学链没有剩余 subset-criticality、window-coherence 或 selector 前提。初稿交付后按 Root 正式顺序 slot 完成下面核验。数学来源编辑限于本新模块和本新 note；核验另产生专属 verification 收据。旧 FourInterior、SingleInterior、OneHeavyAllHull 与其他旧 PASS 来源保持冻结。

## 正式核验收据

最终来源 SHA256：
$\texttt{25de371c7fad631f6217b38f56e3d73e1525b4678a4167d8a1c82e1170994936}$。

三个 selected public 均在 namespace $\texttt{Jsp404.ActualHeavyClumpWeight}$：

* $\texttt{exists\_actual\_heavy\_clump\_weight}$；
* $\texttt{exists\_actual\_F18\_heavy\_clumps\_pure\_light\_card\_ge\_three}$；
* $\texttt{exists\_actual\_F17\_heavy\_clumps\_pure\_zero\_card\_ge\_five}$。

Root 经 Sharp 正式 handoff 唯一 slot。专属 [guard](../verification/oct8-actual-heavy-clump-weight/check.py) 保持 8 GiB 进程树 RSS、180 秒时限与全局最多一个 Lean，每 100 ms 监测。

| 阶段 | 状态 | exit | 秒数 | peak tree RSS KiB |
|---|---|---:|---:|---:|
| strict attempt01 | FAIL，已保留 | 1 | 77.7143 | 4525312 |
| strict attempt02 | FAIL，已保留 | 1 | 85.9880 | 4730576 |
| strict attempt03 | PASS | 0 | 43.2572 | 5330688 |
| genuine normal attempt01 | PASS | 0 | 54.0915 | 4885040 |

两轮修复只涉及 Nat-to-Real numeral 归一、长私有 lemma 的 scoped 600000 heartbeat allowance，以及显式展开 expense/summand 以匹配 finite single-term sum bound。外部 8 GiB/180 秒 hard guard 未放宽，数学与公开接口未变。

首 [781 来源](../verification/oct8-actual-heavy-clump-weight/strict-attempt01.source.lean) / [raw](../verification/oct8-actual-heavy-clump-weight/strict-attempt01.stdout.txt) 和第二轮 [088 来源](../verification/oct8-actual-heavy-clump-weight/strict-attempt02.source.lean) / [raw](../verification/oct8-actual-heavy-clump-weight/strict-attempt02.stdout.txt) 均保留，没有覆盖。

最终 [strict raw](../verification/oct8-actual-heavy-clump-weight/strict-attempt03.stdout.txt) 与 [normal raw](../verification/oct8-actual-heavy-clump-weight/normal-attempt01.stdout.txt) 的三个 selected 都仅依赖
$\texttt{propext, Classical.choice, Quot.sound}$；
均无本模块 own warning、无 resource stop。normal 实际包含 Built own module 与 Build completed successfully。

[checkpoint](../verification/oct8-actual-heavy-clump-weight/checkpoint.json) 记录所有 source/raw/artifact SHA 和资源状态。normal 使用同一 strict PASS 来源；全部 Lean/Lake 退出后已立即正式 release Root，并 FOLLOWUP 唤醒 BetweenAudit 核验下一队列 WordCatalog。之后只作轻量收据与新消费者 SOURCE_ONLY。
