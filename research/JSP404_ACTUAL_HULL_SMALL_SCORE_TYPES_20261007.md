# ActualHullSmallScoreTypes：实际凸包小分数类型

状态：SCOPED_PASS。原候选源码未改，首轮严格检查与首轮正常目标构建均通过，六个 selected exports 仅依赖标准三公理。没有修改旧 PASS 源码、父 Window 或 Git。

源码：[ActualHullSmallScoreTypes.lean](../Jsp000404/ActualHullSmallScoreTypes.lean)。

本模块消费 ActualHullRayWindow.exists_actual_hull_ray_window。公开的三个 producer 都只接受原实际配置、原 Section4Legality、原 fullHull vertex 及必要的原 rowScore；不接受 caller cone、theta 数组或希望得到的类型/partition。

## 1. 最小完整行支撑

exists_actual_hull_full_row_support 内部选取真实 Window W，输出：

* 所有原非中心索引满足 dirRep(o,W.base,c,p,j)=W.theta(j)；
* 完整 directionRow 非空、head=0、getLast=W.width；
* wrapGap=π−W.width，且该值属于原完整行的 cycGaps；
* π−W.width≥λ，其自然 floor 至少为一。

这个桥没有用 subset hull、抽象 sorted row 替代实际行或 dedup 后的行。Window 的真实 left/right 索引提供 0/width 两个 row 成员；完整行的排序给出它们确为极值；width>0 排除 wrapGap 的“全方向相同”例外。

内部再证明 internal gaps 总和为 W.width，完整 row score 等于 internal score sum 加 outside score。

## 2. 实际 gap cut 与 clumps

innerGap_spec 从完整 sorted list 的 internal-gap 成员产生相邻值 a,b，证明：

\[
g=b-a,\qquad
\forall z\in\text{完整 row},\ z\le a\ \lor\ b\le z.
\]

再通过 mem_directionRow 回溯成两个原实际索引，不把相邻数值当 caller 给定的几何点。Clumps 保存真实原 cut endpoints、no-middle、actual cycGap membership、所选 gap 的实际 score、gap 下界与剩余总宽。

Clumps.code 始终按 W.theta(i)≤W.theta(leftRay) 计算，不能由 caller 给任意 Bool class。它提供：

* 两个不同原非中心点分别为 true/false witness；
* 同 code 的实际三点角≤bound；
* 异 code 的实际三点角≥separation。

实际角等于 |theta(j)−theta(i)| 由 Window.actual_direction、非零 actual rays 与 principal-angle 区间内部证明。

## 3. κ1 与 κ2 类型 producer

原 rowScore 可在任意非零 reference e 提供；ChartInvariance.rowScore_directionRow_reference_eq 把它内部转到 W.base。

exists_actual_hull_one_type 输出 internally chosen W 及 LightKind：

| 类型 | 输出 |
|---|---|
| LB | outside score=1，W.width≤π−2λ |
| LI | outside score=0，π−2λ<W.width；实际 clumps，同角≤π−3λ，异角≥2λ，真实两端 witnesses |

exists_actual_hull_two_type 额外只要求 λ>2π/9，输出 HeavyKind：

| 类型 | 输出 |
|---|---|
| HA | outside score=2，W.width≤π−3λ |
| HM | outside score=1，2λ≤W.width≤π−2λ；同角≤π−4λ，异角≥2λ |
| HO | outside score=0，3λ≤W.width；同角≤π−4λ，异角≥3λ |

HM/HO clumps 都保存原实际 scored internal gap 与真实原索引 witnesses。

算术采用直接 score 分拆，未依赖一个额外的 desired-type wrapper：

* internal score sum 一：选出 score 一的实际 internal gap，故其长度≥2λ；
* internal score sum 二且 internal length sum<4λ：若没有 score 二 gap，则每项 score≤1，而且逐项 2λ·score≤gap；求和将强迫 internal length≥4λ，矛盾；
* HO 中 W.width≤π−λ<4λ 来自 λ>2π/9，故必须选到实际 score 二 gap，长度≥3λ。

这个直接证明替代 K3bGeometry 的 rowBig/rowCells 类型算术；没有改变物理输入或接受 caller gap/type。

## 4. 已完成检查的接口

六个 checked exports：

1. Jsp404.ActualHullSmallScoreTypes.exists_actual_hull_full_row_support
2. Jsp404.ActualHullSmallScoreTypes.Clumps.actual_witnesses
3. Jsp404.ActualHullSmallScoreTypes.Clumps.same_angle_le
4. Jsp404.ActualHullSmallScoreTypes.Clumps.different_angle_ge
5. Jsp404.ActualHullSmallScoreTypes.exists_actual_hull_one_type
6. Jsp404.ActualHullSmallScoreTypes.exists_actual_hull_two_type

源码 SHA256 始终为 724b99fef1a206d6815ff0f5342be1e56119783711881b35545430b1d4a3c2ef。

严格检查 13.29 秒，single-Lean 峰值 3,183,738,880 bytes；正常构建 10.98 秒，single-Lean 峰值 3,224,207,360 bytes。正常日志明确包含 own target 的 Built，而非仅 replay。两轮都在单目标 8 GiB / 180 秒限制内，没有资源终止；运行前后源码 hash 一致。

三条 own warnings 如实保留：if_neg 弃用、push_neg 弃用、simpa 简化建议。没有数学或 API 错误，不为清理 lint 改动冻结源码或重复运行。

原始日志、逐轮 exact source snapshots 和旧 SOURCE_ONLY note/receipt 都保存在 verification/oct7-actual-hull-small-score-types。所有 Lean/Lake 进程结束后，sole heavy 已正式交回 Root；这里只发布 scoped six-export 回执，不替换上游 Window 的独立回执。

## 5. 明确不覆盖

当前输出每端至少一个真实 witness，不输出每端至少两点；后者需要原 deletion debt 与 singleton emission consumer。

没有证明 global no-LB、实际 exterior turn sum/K≤8、完整 F18 分支消费者、F17 或原题总下界。这里只能计入这六个 actual producer/consumer 的 scoped checked 结果。
