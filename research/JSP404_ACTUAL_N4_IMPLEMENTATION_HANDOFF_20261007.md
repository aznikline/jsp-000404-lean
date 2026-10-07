# 实际 n4 证明的接续接口

截至 2026-10-07 本批有限重放及实际消费者分别核验完成时。原题任意 N 下界尚未完成；原 MainTheorem 的 N≥17 分支仍含 sorry。本文区分已通过核验的接口与仍需实现的证明，不能作为最终获奖证明。

## 已推送的基点

分支 `review/jsp404-proof-continuation-20261004`，最近已推送提交 `2cd3def1ab6a6752766918f210a71b1f4e087da9`。该基点之前的整库构建为10437 jobs，统一标准公理审计为783个声明；之后另有10个 standalone 声明分别通过严格及正常检查。原下界负控制只报 sorryAx。原 Statement、MainTheorem 与引入的 Sendov 定义未改。本次新有限检验与消费者已统一接入：10662-job 默认构建及1707个声明 trust-zero 公理审计通过，原下界仍只报sorryAx；新提交待推送，回执见 `JSP404_TERMINAL_GEOMETRY_INTEGRATION_RECEIPT_20261007.json`。

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

`ActualPureLightBlock` 两个最终消费者已两路检查及统一审计通过：非空纯原hull-light块在外中心满足3λ cross时至少四点，进而排除原F18唯一heavy/全hull/actual≥3λ角子分支。其余最终消费者按 `JSP404_F18_COMPLETE_PAPER_MAP_20261007.md` 及其中七份冻结 paper 实现。每个类、角度、原最近邻及多删费用必须来自这些实际生产者；不得把 paper 的希望结论作为调用者前提。原 hull 与子集 hull、原分数与子集分数分别保持清楚。尤其不能使用已被实际 F16 五点负控推翻的“SAT+四个 LI 不可存在”。

## F17：真正仍缺的数学步骤

`ActualZeroPairDeletionBudget` 已真通过。两个原 zero target 删除后，只有一单位增长预算，正原分数的 surviving row 不许增长；原 zero row 至多一个增长一。

这不等于“原 F17 所有 incoming gains 全零”。最小原分数零只保证删除 zero target 的整列零增益。exact-flat inflation 到十七点也不自动继承原 minimum_card、proper-subset cap 或全零 gain。

`ActualInteriorZeroPartition` 已通过严格检查及正常构建：内部真实三类、实际直径端点、总 span≤π−3λ、异类角≥2λ与 singleton 原实际正增益全部核验。`ActualHeavyNearestExclusion` 与 `ActualHullWindowScoreLower` 也已核验，分别供非锐 heavy 最近邻排除和实际窗口的独立尺度分数下界。这三个模块先作为 standalone producer 发布，现已加入默认 root 并进入1707个声明的统一审计；它们仍不等于 F17 最终消费者。

sector/fan-tail、complete heavy clump 重量至少五等仍见 `JSP404_N4_LOW_F17_GEOMETRY_OCT7.md` 的纸面论证。尚缺从实际几何选出违反原删除预算的点集。不要把“某 run 只有两个原 hull 点”写成“该 run 只有两个实际点”，也不要把原 hull 点默认当角向极端。

## HIGH 的八点 R2：只需三个实际排名情形

已核验的 `ActualN4R2RankRegions` 从原实际 SAT anchor、两条原 defect-two 行内部产生排序与区域，低行排名只可能为 (0,1)、(0,6)、(5,6)。它不对裸 GenericModel 宣称这三个情形穷尽。

24698-word Catalog/Tree/ModelCatalog 的覆盖以及全部193个 LeafChecked shards 已逐一通过严格检查与真实正常构建。每个 block 使用紧凑本地 cycle library、独立 named leaf 和平衡分类组合，关闭 Elab.async。合计214个必要模块、894个选定声明已经冻结，见 `JSP404_N4_R2_BETWEEN_REPLAY_FINAL_FREEZE_20261007.json`。先前失败的 global128/global32/compact128 与首轮 Fin 值归约错误均保留，未改写为成功。

`N4R2BetweenTerminal.between_pure_tail_impossible` 已通过两路检查：任意 GenericModel 7 4 中排名0和6的行 defect=2，其余五行 defect=4，即导出 False；不需调用者提供 word、rowData、cycle 或 solver-success 前提。`ActualN4BetweenZeroTailClosure` 的两个声明也已严格及正常检查通过，内部从原实际八点 SAT anchor 构造 chart、reference 和 rank sigma，将该有限结果接回原参考下的原始行。对应回执为 `JSP404_ACTUAL_N4_BETWEEN_ZERO_TAIL_CLOSURE_RECEIPT_20261007.json`。这仍仅关闭 between 分支，不能称作完整八点容量或任意 N 下界。

`ActualNoThreeNonacuteHeavy.no_three_nonacute_heavy` 已严格及正常检查通过：原 n4 LOW 最小反例中不可能选出三个原 score2 且各有实际角≥2λ见证的点。它不需要F17/F18、总heavy数量或调用者给定clumps。通用 n≥4 的实际最大得分两簇生产者 `ActualMaximalLowRowClumps` 也已两路通过；后续通用三点几何及 Model 消费者也已两路检查并接入统一审计，实际clumps与companion均在原Model内部生成。
下一步使用独立新 generator/decoder 处理 outer(0,1)，由通用反射接 (5,6)。旧 catalog 与所有 PASS 字节保持不变。旧 tail 证书的静态复用统计只是候选，必须经过新角色对应的 typed decoder 和 kernel 检查；不能把 Python 筛选数当证明。


## 后续已核验局部消费者

`JSP404_F17_F18_LOCAL_CONSUMERS_RECEIPT_20261007.json` 记录四个新模块、六个选定声明，10666-job 默认构建与1713个声明统一标准公理审计通过，原下界仍只报sorryAx。

- `ActualRigidFourGeometry` 内部推出所选四个原rigid点在2λ尺度下全零分、全为子集凸包点、完整凸包窗口宽度至少2λ；不推出任意三角形的角≥2λ。
- `ActualPureInteriorZeroBlock` 从原Model内部取得零target incoming gain，证明满足外中心3λ隔离的非空纯原interior-zero块至少六点。`FiveTwoClassPairing` 是其独立有限计数工具。全局F17选择仍未知。
- `ActualF18ThreeHeavyAcute` 排除三heavy且所有light均非原Hull的六点子情形，并从三个原heavy内部生成一个HA窗口。其它凸包点数分支仍待接通。

新SingleInterior、TwoInterior、RigidFourNonapex和八点outer重放仍处候选/检查阶段；未纳入此批已证范围。
