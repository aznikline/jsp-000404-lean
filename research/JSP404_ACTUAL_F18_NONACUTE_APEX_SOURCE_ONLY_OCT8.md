# F18 weighted nonacute-apex 与唯一 heavy 消费者

日期：2026-10-08。初稿为 SOURCE_ONLY；后续按 Root 正式唯一 slot 完成 first strict 与 first genuine normal，两个公开消费者均实际 PASS。未运行 Git。

新来源为 [ActualF18NonacuteApex.lean](../Jsp000404/ActualF18NonacuteApex.lean)。它只消费原实际模型以及已经核过的 ClassWeight、InteriorApex、HeavyClumpWeight、PureLightBlock 与 OneHeavyAllHull APIs。HeavyClumpWeight 最终通过来源 25de 开头保持冻结。

## 任意 F18 profile 中的 nonacute heavy 都不在 interior apex

公开入口
$\texttt{actual\_nonacute\_heavy\_not\_in\_interior\_apex}$
只接受原 Model/F18、原 interior 点 $P$、原 score-two heavy $H$ 和 $H$ 处一个实际角至少为 $2\lambda$。不要求唯一 heavy，也不接受 caller partition、clump 或权重预算。

入口内部使用 Sharp 的固定 actualClassWeight。该数据同时包含原实际 partition、原索引 class Finsets、每类质量至少 $4$ 和三类总质量 $16$。因此原 apex 质量至多为 $8$。

假设 $H$ 在 $P$ 的 apex。内部 HeavyClumpWeight 给 $H$ 的两个实际端，各原质量至少为 $6$。取不含 $P$ 的端 $C$。若 $q\in C$ 不在 $P$ 的 apex，则

\[
\angle HPq\ge3\lambda,\qquad
\angle PHq\ge2\lambda,
\]

两角和至少为 $5\lambda>\pi$。所以 $C$ 全在 $P$ 的 apex，并且 $H\notin C$。该 apex 的质量至少为

\[
4+W(C)\ge10,
\]

与上界 $8$ 矛盾。

公开输出直接是 heavy 不属于内部 canonical apex Finset，没有要求 caller 提供点不等式或指定 Data。

## 整个唯一 nonacute heavy F18 profile

第二入口
$\texttt{actual\_F18\_unique\_nonacute\_heavy\_false}$
接受原 Model/F18、原 score-two heavy $H$、所有其他原点 score-one，以及 $H$ 处一个实际角至少为 $2\lambda$。不接受原 interior 数量或 hull 布局。

若全部原点在 fullHull，使用已核 OneHeavyAllHull。否则内部取一个原 interior $P$：

1. Sharp 的 apex-fullHull 输出给原 apex 全是原 hull 点。
2. 第一消费者排除 $H$ 在 apex；唯一 heavy profile 因而使该 apex 全为原 HullLight。
3. PureLightBlock 给 apex 至少四点、原质量至少 $8$。
4. 在 $H$，$P$ 和全部 apex 点同端：实际 $3\lambda$ apex/nonapex 角与异端至少 $2\lambda$ 的三角形排除强迫这个结论。
5. 该端质量至少为 $2+8=10$，另一端质量至少为 $6$。两个端完整分割除 $H$ 外的原点，其总原质量恰为 $18-4=14$，矛盾。

该链不按原 interior 个数拆分；实际 wide-angle 条件覆盖 HM/HO nonacute 分支，不处理不满足该条件的 HA heavy。

## 数据一致性与核验边界

ClassWeight 与 Sharp-apex 输出统一使用同一个内部 canonical actualClassWeight，避免不同 partition witness 的无证识别。Heavy clump 与 interior class 的传递只通过真实角度进行，不要求两个 angular windows 相同。

当前没有 selector、NN、subset-criticality 或未证质量前提。初稿之后已按 Root 正式队列完成下面的实际核验。数学来源编辑只限本新模块和本新 note；核验另产生专属 verification 收据，没有修改其他旧 PASS 来源。

## 正式核验收据

来源从初稿起未改，最终 SHA256：
$\texttt{81d57f6a76b22cac68812da5d93f086184d640bddabebb1f784bad5eeca52724}$。

两个 selected public 都在 namespace $\texttt{Jsp404.ActualF18NonacuteApex}$：

* $\texttt{actual\_nonacute\_heavy\_not\_in\_interior\_apex}$；
* $\texttt{actual\_F18\_unique\_nonacute\_heavy\_false}$。

Root 直接正式授予唯一检查 slot。专属 [guard](../verification/oct8-actual-f18-nonacute-apex/check.py) 保持全局最多一个 Lean、8 GiB 进程树 RSS 与 180 秒时限，每 100 ms 监测。

| 阶段 | 状态 | exit | 秒数 | peak tree RSS KiB |
|---|---|---:|---:|---:|
| first strict attempt01 | PASS | 0 | 57.5070 | 5224576 |
| first genuine normal attempt01 | PASS | 0 | 67.0448 | 4941104 |

两个 selected 在 [strict raw](../verification/oct8-actual-f18-nonacute-apex/strict-attempt01.stdout.txt) 与 [normal raw](../verification/oct8-actual-f18-nonacute-apex/normal-attempt01.stdout.txt) 中均仅依赖
$\texttt{propext, Classical.choice, Quot.sound}$，
没有本模块 own warning 或 resource stop。normal 实际包含 Built own module 和 Build completed successfully，没有把 replay 当作 own build。

[checkpoint](../verification/oct8-actual-f18-nonacute-apex/checkpoint.json) 记录 exact source/raw/artifact SHA 和资源状态；两个 source snapshots 均为相同的初稿。没有失败候选或快修。全部 Lean/Lake 退出后已立即正式 return Root；没有自行接 Assembly 或 Root full check。

这两个结果实际关闭任意 F18 profile 的 nonacute-heavy-apex 位置，以及唯一 heavy 的整个 HM/HO 分支。未据此声明 HA 分支、F17 分支或整个容量问题完成。
