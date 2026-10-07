# Actual F18：唯一 heavy、全部原点在 fullHull

日期：2026-10-08。初稿为 SOURCE_ONLY；随后按 Root 正式授权完成 first strict 和 first genuine normal，均实际 PASS。未运行 Git。

新来源为 [ActualF18OneHeavyAllHull.lean](../Jsp000404/ActualF18OneHeavyAllHull.lean)，唯一公开入口
$\texttt{actual\_F18\_one\_heavy\_all\_hull\_false}$。

接口只接受原 cap-16 minimal actual Model、原 $F=18$、原 score-two 点 $p$，以及每个其他原点的 score-one 和原 fullHull 身份。没有 supplied wide angle、类型、clump、整数权重、点数、较低 cap 或子集 counter 前提。SingleInterior 的最终通过来源保持冻结。

## 内部原点数与分类

原 F18 frame 与输入 profile 给出 heavy 集恰为 $\{p\}$，所以

\[
N+1=9,\qquad N=8.
\]

这里 $N$ 是原点数，等式左边额外的 $1$ 是 heavy 数。原 heavy 的 fullHull 身份也由 frame 得到，因此八个原点都可以作为原 hull vertices 选入 turn budget。

实际 hull-two Types 生产器内部给出 $p$ 的 HA、HM 或 HO 类型。

## HA 与 HM：实际整数 turn budget

对八个原 hull vertices 使用恒等选择。其他七点采用整数权重 $1$；它们的实际角上界由原 legality 给出 $\pi-\lambda$。

* HA 时，$p$ 的原实际 full cone 至多为 $\pi-3\lambda$，故在 $p$ 采用权重 $3$，总整数权重 $K=7+3=10$。
* HM 时，$p$ 的原实际 full cone 至多为 $\pi-2\lambda$，故采用权重 $2$，总整数权重 $K=7+2=9$。

两种情况都把实际角上界交给已经存在的
$\texttt{ActualHullTurnBudget.selected\_hull\_integer\_budget\_le\_eight}$。
其内部可独立选择物理 windows；本消费者没有要求这次选择与 Types producer 的 window 相同。实际全原角上界已经对每个被选择顶点成立，包括后来内部挑选的 boundary witnesses。

得到 $K\le8$，分别与 $K=10$、$K=9$ 矛盾。

## HO：内部构造 actual wide pair

HO 给原 window 的宽度至少为 $3\lambda$。其两个真实 boundary rays 来自互异原点，且 window width 等于它们在 $p$ 的实际夹角。因此内部构造出一个 actual angle 至少为 $3\lambda$，再交给已经核过的
$\texttt{ActualPureLightBlock.actual\_F18\_one\_heavy\_all\_hull\_three\_scale\_angle\_false}$。

该 consumer 排除 HO 分支。三个分支穷尽，所以原唯一 heavy、其他七点均为原 HullLight 的全部 allHull 分支被排除。这里的 wide angle 是内部结论，不是 caller 前提。

## 核验范围

本模块初稿只作 source-only 交付；后续正式授权后的实际核验见下面收据。不声称其他带 interior 的 one-heavy 分支已经由此模块闭合。数学来源编辑只限此新来源和本新 note，核验另生成专属 verification 收据；没有改动其他人的模块或已冻结来源。

## 正式核验收据

来源从初稿起未改，最终 SHA256：
$\texttt{d58028ad9bec12d69cc933863f7f4a410e727674bc8a0853f2fc3d8a408d93d4}$。

唯一 selected public：
$\texttt{Jsp404.ActualF18OneHeavyAllHull.actual\_F18\_one\_heavy\_all\_hull\_false}$。

Root 经 sharp-geometry 的 formal sole handoff 授权核验。专属 [guard](../verification/oct8-actual-f18-one-heavy-all-hull/check.py) 在启动前排除其他 Lean，运行中每 100 ms 检查全局最多一个 Lean、8 GiB 进程树 RSS 和 180 秒时限。

| 阶段 | 状态 | exit | 秒数 | peak tree RSS KiB |
|---|---|---:|---:|---:|
| first strict attempt01 | PASS | 0 | 24.9400 | 5965696 |
| first genuine normal attempt01 | PASS | 0 | 33.2903 | 5793792 |

两次均无 resource stop、无本模块 own warning；selected 仅依赖
$\texttt{propext, Classical.choice, Quot.sound}$。
[normal raw](../verification/oct8-actual-f18-one-heavy-all-hull/normal-attempt01.stdout.txt)
实际包含 Built own module 和 Build completed successfully，没有把 replay 当作本模块构建。

[checkpoint](../verification/oct8-actual-f18-one-heavy-all-hull/checkpoint.json)
记录每轮 exact source、raw、artifact SHA 与资源状态；两个 source snapshots 都是相同的初稿 SHA。没有失败候选或快修。全部 Lean/Lake 退出后已立即正式 return Root，之后只做轻量收据。

此收据只覆盖公开的一-heavy allHull 消费者，不独立声明整个 F18 或全部点数问题完成。
