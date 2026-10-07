# 实际 n4 证明的接续接口

截至 2026-10-07 本批实际生产者核验完成时。原题任意 N 下界尚未完成；原 MainTheorem 的 N≥17 分支仍含 sorry。本文区分已通过核验的接口与仍需实现的证明，不能作为最终获奖证明。

## 已推送的基点

分支 `review/jsp404-proof-continuation-20261004`，提交 `3ef7cd5e94953abdf4d3aab409b8df82230098d3`。10429-job 整库构建、756 个声明的标准公理审计通过；原下界负控制只报 sorryAx。原 Statement、MainTheorem 与引入的 Sendov 定义未改。

## F18：已有完整纸面分支，实际生产者正在接通

`ActualF18Frame.actual_f18_frame` 已严格检查及正常构建通过：从原实际最小反例与 F18 内部推出所有原分数为一或二、heavy 均在原满凸包、heavy 数 t≤3，以及 N=9−t。因此仅需处理 N=6,7,8,9。

以下模块也已分别通过严格检查及正常构建，但本节的后续新模块尚未全部并入上述远端基点：

- `ActualInteriorOnePartition`：原内部 score-one 中心内部产生三类、真实角度界与 singleton 正增益。
- `ActualHullRayWindow`、`ActualHullTurnBudget`：原满凸包真实边界射线、圆周预算与 hull≤8；整数预算的接口带 r≥2。
- `ActualHullSmallScoreTypes`：原 hull κ1 的 LB/LI 与 κ2 的 HA/HM/HO，含真实 clumps 和角度约束。
- `ActualHullConeDeletion`：从实际窗口内部产生非零 bisector；宽度≤π−2λ产生真实 emitter。
- `ActualF18LightHullClumps`：原 F18 最轻点零 incoming gains 排除 LB，内部产出 hull light 的 LI 两团射线。
- `ActualProperSubsetDeletionBudget`：所有保留至少三点的真子集，直接使用原 minimum_card。净加权增长 E 与原超额满足 E+(F−16)≤原删除重量；F18 时为 E+2≤删除重量。

`ActualInteriorOneClassSize`、泛化后的 `ActualF18HeavyZeroGain`、`ActualMixedRigidCardinality` 也已分别通过严格检查及正常构建。它们分别给出纯 light 类至少两点、heavy observer 对所有 target 零增益、原 interior-one 与原 heavy-wide 混合刚性集≤4。heavy 零增益的泛化接口不需要 F18，直接适用于原 n4 LOW 最小反例。

最终消费者按 `JSP404_F18_COMPLETE_PAPER_MAP_20261007.md` 及其中七份冻结 paper 实现。每个类、角度、原最近邻及多删费用必须来自这些实际生产者；不得把 paper 的希望结论作为调用者前提。原 hull 与子集 hull、原分数与子集分数分别保持清楚。尤其不能使用已被实际 F16 五点负控推翻的“SAT+四个 LI 不可存在”。

## F17：真正仍缺的数学步骤

`ActualZeroPairDeletionBudget` 已真通过。两个原 zero target 删除后，只有一单位增长预算，正原分数的 surviving row 不许增长；原 zero row 至多一个增长一。

这不等于“原 F17 所有 incoming gains 全零”。最小原分数零只保证删除 zero target 的整列零增益。exact-flat inflation 到十七点也不自动继承原 minimum_card、proper-subset cap 或全零 gain。

目前新 `ActualInteriorZeroPartition` 正在实现实际三类结构；sector/fan-tail、complete heavy clump 重量至少五等仍见 `JSP404_N4_LOW_F17_GEOMETRY_OCT7.md` 的纸面论证。尚缺从实际几何选出违反原删除预算的点集。不要把“某 run 只有两个原 hull 点”写成“该 run 只有两个实际点”，也不要把原 hull 点默认当角向极端。

## HIGH 的八点 R2：只需三个实际排名情形

已核验的 `ActualN4R2RankRegions` 从原实际 SAT anchor、两条原 defect-two 行内部产生排序与区域，低行排名只可能为 (0,1)、(0,6)、(5,6)。它不对裸 GenericModel 宣称这三个情形穷尽。

现有 24698-word Catalog/Tree/ModelCatalog 的覆盖已经 kernel 闭合；20027 条实际引用 cycle 数据也通过了类型核验。全部 leaf 排除和最终 between theorem 仍未完成。

验证瓶颈的实测记录必须保留：global128、global32、compact-local128 的整体闭合检查触及内存上限，均为 NOT_PROVED。独立 named 单 word 的 DirectProbe 已通过，峰约 2.45 GiB。首 named128 同步版本峰约 2.52 GiB，未触内存上限，但组合定理仍有显式 Fin 值归约错误，整模块尚不能计 PASS。接续方案是在每个 block 内使用紧凑本地 cycle 索引、独立 namedLeaf 与每 word 定理，关闭 Elab.async 后以平衡分类组合 point_checked。`N4R2RowDataReplaySoundness.leafCheck_sound` 对任意 Library 成立，故不需要把 local library 证明为全局表的拷贝；每条 origin/weight/strict 匹配仍由 kernel 执行。

between 真闭合后，再用独立新 generator/decoder 处理 outer(0,1)，由通用反射接 (5,6)。旧 catalog 与所有 PASS 字节保持不变。旧 tail 证书的静态复用统计只是候选，必须经过新角色对应的 typed decoder 和 kernel 检查；不能把 Python 筛选数当证明。
