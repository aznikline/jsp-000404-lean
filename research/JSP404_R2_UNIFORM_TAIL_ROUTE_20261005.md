# R2 全 n 尾部：两低行的坐标投影路线

这是只读纸面推导，**未编译、未运行 solver、未修改任何证明源**。
它给出一个可落实的 BETWEEN 分支引理，并明确未闭合的几何输入；不声称
已经证明全 R2 容量，也没有把抽象台账当成实际平面反例。

记实际合法 `SatChart` 的 anchor 为 v，两条缺陷 2 行为 a、b，其余点为
T，且 θ_a<θ_b。令 β=π−nλ∈[0,λ)、Q=2^(n−2)，
w_i=2^(n−d_i)。Anchor 与两低行总重为 2Q+Q+Q=4Q，所以目标正是
Σ_{i∈T}w_i≤Q。尾行 d_i≥3，并不等于 d_i=3。

## 可落实的分支：保留 n 格，只删两个颜色坐标

在 BETWEEN 类 θ_a<θ_t<θ_b（t∈T）中，定义 Φ_ij 为 chart 中的真实
`dirRep`。取现有合法公共分箱，start=λ、格宽 w<λ、格数 n。无需新几何
假设即可选取：

```text
W = π−2λ+β
w = (W + π−λ)/(2n)
0 < w < λ,  W ≤ nw < π−λ.
```

因此所有非 anchor chords 落在 [λ,λ+nw]，且末端小于 π。
`occupied_bins_le_rowDefect` 给每个非 anchor 行 A_i≤d_i；两低行各
至多占两个颜色。这用的是实际完整 score，不假定两行均属于 F=n、B=2。

记 χ(i,j)=uniformBin λ w n (Φ_ij)，k₀=χ(a,b)。新增候选引理的输入是
以下**局部可检查条件**：

```text
∀t∈T, χ(a,t)≠k₀ 且 χ(t,b)≠k₀.
```

条件不是 clump、strict slack 或容量假设。它尚未由全部 R2 前提推出。
在此条件下，尾质量界的推导完整如下：

1. 若 T 非空，两低行的至多两个颜色各含 k₀，以及唯一另色 k_a、k_b；
   故所有 χ(a,t)=k_a、χ(t,b)=k_b。T 为空时质量界直接成立。
2. `up_cap` 用于 a<t<b，给 |Φ_at−Φ_tb|≥λ。同一格内两值之差≤w<λ，
   因而 k_a≠k_b。
3. 对 θ_t<θ_u 的两个尾点，`up_cap` 用于 a<t<u 与 t<u<b，分别给
   χ(t,u)≠k_a、χ(t,u)≠k_b。反序由 Φ 对称处理。因此**所有尾部之间的
   边均避开这两个固定颜色**。
4. 每个尾行的非 anchor 占用集恰为 `{k_a,k_b}` 与尾部自身占用集的
   不交并；若后者大小为 A_i^T，则 d_i≥2+A_i^T，故
   `n−d_i ≤ (n−2)−A_i^T`。
5. 原几何 bin graphs 的每对反位分离发生在该对尾点的边颜色上，该颜色
   不在 `{k_a,k_b}`。删去两个公共坐标，余坐标重新标为 Fin(n−2)，分离
   仍成立。应用 `sum_free_binary_coordinates_le` 或
   `weighted_interval_packing`，得

```text
Σ_{i∈T} 2^(n−d_i)
  ≤ Σ_{i∈T} 2^((n−2)−A_i^T)
  ≤ 2^(n−2) = Q.
```

这是坐标投影，**不是**把同一行的长 π 区间改成 n−2 个短格。原 n 格
full-row 空格预算仍完整使用，因此没有端点收费漏洞，也覆盖任意深尾
d_i≥3。实现时应保留实际 bin graph 的二着色，不得另行假定抽象 bits
分离。

建议接口名：`r2_between_tail_capacity_of_avoids_low_shared_bin`。依赖：
`MixedStarExclusion.up_cap`（194 行）、`phi_comm`、
`OneSaturatedHigh.occupied_bins_le_rowDefect`（4153 行）、
`BinGraphs.directionBinGraph_colorable/cover` 与
`ThirdParty/Sendov/JSP404/BinaryEncoding.lean` 的计数引理。需要补的只是
两个 occupied-colour 唯一性、Fin(n−2) 重标与 full-row/尾行占用集等式。

所以 BETWEEN 的真正 over-capacity 残余必含某条 low–tail 边与 AB
共享颜色；否则上述分支已经关闭。ABOVE/BELOW 类也能用同一投影，但还
须明确证明 k_a≠k_b；其同色另一色情形不能凭 BETWEEN 论证排除。

## 共享 AB 颜色的局部角度压缩

这一残余不能直接声称有 slack。可先落实另一个只用实际 corridor 与
betweenness 的局部引理。设 θ_a<θ_t<θ_u<θ_b，且

```text
Φ_at < Φ_ab < Φ_tb,
Φ_ub < Φ_ab < Φ_au.
```

`up_trans` 的 a<t<u 分支强制 Φ_au<Φ_tu，t<u<b 分支强制 Φ_tb<Φ_tu。
`up_corridor` 在 t<u 与 u<b 上使用同一个 θ_u，给

```text
Φ_tu ≤ π−λ+θ_u,  Φ_ub ≥ θ_u+λ,
Φ_tu−Φ_ub ≤ π−2λ.
```

故三个正差 `Φ_au−Φ_ab`、`Φ_tb−Φ_ab`、`Φ_ab−Φ_ub` 都严格小于
π−2λ。由 π<(n+1)λ，三者的 Nat floor（除以 λ）均≤n−2，gapScore 均
≤n−3。镜像方向用 t<u 的 lower corridor 与 a<t 的 upper corridor，
同理压缩 `Φ_at−Φ_ab`、`Φ_ab−Φ_au`、`Φ_ab−Φ_tb`。

该引理不要求 puretail、clump、strict slack 或 cap；它能阻止指定
low-row 过渡 gap 单独承担全部 n−2 score。它还没有推出第二个 strict
margin，也没有证明所有尾点统一避开 AB 颜色。

## 当前捷径的确切障碍

- `rowDefect=2` 只推出 Type I：B=1、F=n−1，或 Type II：B=2、F=n
  （`K3bGeometry.rowDefect_eq_two_type`，1979 行）。不能默认 fullfloor/
  support2；上面的 occupied≤2 推导兼容两类。
- 现有 `linearGapScore_le_empty_of_interval` 对一锚行的两端余量各要求
  ≤λ。若直接令 m=n−2、w<λ，则得到
  `π≤(n−2)w+2λ<nλ≤π`，前提矛盾。现有 two-anchor 消费者的短窗口也
  不能自动搬到这里：删 v 后两 low 只有在另证双 big ends 时才升为两条
  defect1 anchors；真正 tail-only 消费还欠真实双端排列与共同 corridor。
- `r2_tail_delete_closed`（FivePointCapacity:2290）确实保 anchor1/
  low2/其余≥3，但台账（2422 行）是 `W_q⁻+w_q=W+G_q`。要将原尾质量
  送入较小配置的界，还需 `G_q≥w_q`，不是仅合法删除。
- 强归纳下可用已有 `minimal_excess_single_delete`（2560 行）：选最小
  dyadic weight u，较小配置界作为明确 IH，得 W=Q+u 且该删除的全部尾
  gains 为零。这个结论不是新证的几何进展。n=4、Q=4、五条 weight1 尾
  行给 W=5、每次删一条剩4、G=0，与所有台账和删除闭合条件相容；这只是
  **算术障碍模型，不是实际平面反例**。
- `r2_tail_delete_all_gains_zero`（2730 行）需要所有 tail defect=3，
  不能用于上述 defect4 尾。一般 minimum-tail 的 actual zero-gain bridge
  可由明确 IH 与已有台账接出，但还需要真实几何把共享-bin witness 转成
  正 gain、big-end promotion 或满足已证 slack consumer 的条件。

结论：可以先实现上述 BETWEEN 两坐标投影分支与局部过渡-gap界，避免
重做 n=3、小 N 或 dyadic 家族。**全 R2 尾界仍缺共享低低 bin 残余的真实
几何排除，以及 ABOVE/BELOW 的同另色情形；本报告没有补成全 N 证明。**
