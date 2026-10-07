# Actual F18：唯一 heavy、四个原 interior

日期：2026-10-08。初稿为 SOURCE_ONLY；后续按 Root 正式唯一 slot 完成 strict 与 genuine normal，均实际 PASS。未运行 Git。

新来源为 [ActualF18OneHeavyFourInterior.lean](../Jsp000404/ActualF18OneHeavyFourInterior.lean)，唯一公开入口
$\texttt{actual\_F18\_one\_heavy\_four\_interior\_false}$。

入口接受原 Model/F18、一个原 score-two 点 $p$、其他原点全 score-one、一个 injective $\mathrm{Fin}\,4$ 原 interior 选择，以及在 $p$ 和这四点之外的每个原点的 fullHull 身份。所有点数、partitions、nonapex 结论和 class Finsets 都在内部构造；没有类型、实际 wide angle、caller clump 或 class-size 前提。

## 原八点与 R4 输出

原 F18 frame 给出 heavy 集恰为 $\{p\}$、原点数 $N=8$，以及 $p$ 的原 fullHull 身份。因此这四个原 interior 都与 $p$ 不同，且都是 light。

已经核过的
$\texttt{ActualRigidFourNonapex.actual\_rigid\_four\_nonapex}$
在每个被选择的原 interior 点 $X$ 内部给出实际三类 partition，并证明其余三个被选择点都在 $X$ 的 nonapex。

## heavy 必须在每个 apex

固定一个被选择点 $X$。假设 $p$ 不在其 apex。则 apex 中的每个点：

* 不等于 $X$，由实际 target subtype；
* 不等于其余三个 selected interiors，由 R4 nonapex；
* 不等于 $p$，由当前假设。

所以 apex 全是其他原 HullLight，并且属于八点中除去 $p$ 和四个 selected interiors 之外的三点。实际 partition 的 apex 非空，且与所有 nonapex 射线的实际角至少为 $3\lambda$。将它作为真实原 Finset 交给已经核过的 PureLightBlock 消费者，得到 apex 至少四点。

源码通过有限集计数表达三点上界：四点 image 的基数为 $4$，插入原 heavy 后基数为 $5$；apex 与这五点不交，因此 apex 基数加 $5$ 至多为 $8$，矛盾。

故原 heavy $p$ 在四个 selected interior 的每一个 apex。

## 两个实际大角矛盾

任取其中两个不同原点 $X,Y$。R4 仍给出 $Y$ 在 $X$ 的 nonapex，$X$ 在 $Y$ 的 nonapex；而 $p$ 在两者的 apex。因此三角形 $pXY$ 满足

\[
\angle pXY\ge3\lambda,\qquad
\angle pYX\ge3\lambda.
\]

两角和至少为 $6\lambda>\pi$，矛盾。这排除整个明确的 one-heavy、exact-four-original-interior profile，完全不区分 heavy 的 HA/HM/HO 类型。

## 核验范围

数学链没有剩余 selector 或 nearest-neighbor 前提。初稿按 SOURCE_ONLY 交付，随后按 Root 正式顺序 slot 完成下面的核验；没有编辑已经冻结的 SingleInterior、OneHeavyAllHull 或 R4 producer。

本入口保留“其余原点是 fullHull”的 exact-four profile。尚未在这个文件中增加通过 selected-interior cardinality bound 自动导出该条件的加强 wrapper。

## 正式核验收据

最终来源 SHA256：
$\texttt{6cfa3b5fb963e564439a97be798cfc94b217f0f040b43d56e04c665e6b9564a6}$。

唯一 selected public：
$\texttt{Jsp404.ActualF18OneHeavyFourInterior.actual\_F18\_one\_heavy\_four\_interior\_false}$。

Root 正式授予 slot 后，专属 [guard](../verification/oct8-actual-f18-one-heavy-four-interior/check.py) 在启动前排除其他 Lean，运行期间每 100 ms 检查全局最多一个 Lean、8 GiB 进程树 RSS 和 180 秒时限。

| 阶段 | 状态 | exit | 秒数 | peak tree RSS KiB |
|---|---|---:|---:|---:|
| strict attempt01 | FAIL，保留来源与 raw | 1 | 36.9422 | 6231824 |
| strict attempt02 | PASS | 0 | 19.4746 | 6394656 |
| genuine normal attempt01 | PASS | 0 | 21.6505 | 6298304 |

首次失败只有一个已更名的 Mathlib API：原写 $\texttt{Finset.card\_insert\_of\_not\_mem}$ 改为当前实际名称 $\texttt{Finset.card\_insert\_of\_notMem}$。只修正这一名称，公开接口与数学证明未变；原 SHA339 开头的 [exact source](../verification/oct8-actual-f18-one-heavy-four-interior/strict-attempt01.source.lean) 和 [raw](../verification/oct8-actual-f18-one-heavy-four-interior/strict-attempt01.stdout.txt) 已保留。

最终 [strict raw](../verification/oct8-actual-f18-one-heavy-four-interior/strict-attempt02.stdout.txt) 与 [normal raw](../verification/oct8-actual-f18-one-heavy-four-interior/normal-attempt01.stdout.txt) 的 selected 仅依赖
$\texttt{propext, Classical.choice, Quot.sound}$，
均无本模块 own warning、无 resource stop。normal 实际包含 Built own module 与 Build completed successfully，没有把 replay 当成本模块构建。

[checkpoint](../verification/oct8-actual-f18-one-heavy-four-interior/checkpoint.json) 记录每轮 source/raw/artifact SHA 与资源状态。所有 Lean/Lake 退出后已立即正式 release Root，并按 Root 明确 delegation FOLLOWUP 唤醒 integration 检查下一组 five-module 首队列；之后只做轻量收据。

核验只覆盖此 exact-four-interior 消费者，不独立声明整个 F18 或全部一-heavy 分支完成。
