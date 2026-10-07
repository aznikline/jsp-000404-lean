# n4 LOW F18：纸面闭合集与实现依赖图

日期：2026-10-07。状态：PAPER_MAP，不是完整 Lean/Kernel 闭合证明。

范围仅为 minimal actual n4 LOW counter 的 F18 分支，即
$2\pi/9<\lambda\le\pi/4$、最小原 row score 为一、原 potential 为十八。这里不宣布 F17、整个 n4 LOW、所有 strip 或原题任意 N 下界已经解决。

本次只读审查没有运行 Lean、Lake、Git 或 quota。所有检查状态来自已保存的 exact-source receipt；没有把静态源码或纸面论证计入 Kernel PASS。旧冻结 paper 未改。

## 1. 当前结论分层

1. **PAPER 闭合**：在下述实际几何 producer、满凸包类型及原 counter debt 前提下，F18 的 $t=0,1,2,3$ 全部排除，点数分别为 $9,8,7,6$。
2. **已有 scoped checked pieces**：actual interior 原射线窗口与最近邻桥、common-cone emission、显式 angle-gap premise 的 rigid cardinality 等已有精确回执。
3. **尚不可算全 Kernel**：实际三 classes/apex/singleton producer、实际满凸包 cone/type/curvature 及各 paper 分支的最终 typed consumers 尚未全部连接。角度二择并不自动构成三 classes certificate。

## 2. 七份冻结 paper 及精确 scope

| 文件 | 覆盖 | SHA256 |
|---|---|---|
| [mixed hull](JSP404_F18_MIXED_HULL_OCT6B.md) | 全 $t=3,N=6$；通用 debt、nearest、hull 类型，及后续被新 note 继续排除的残余 | bd02ed011e6c4013250e6165526861c49af1c4aa22b0dc0d8caf4be7feb1eaa9 |
| [N7 四顶点](JSP404_F18_T2_N7_OCT7.md) | $t=2,N=7,h=4$ | 20d8dd172c0d32c63e98cc357ae69c41918cbef769009d3bc3f6f60d651cf893 |
| [N7 HO](JSP404_F18_T2_N7_HO_OCT7.md) | 七点全部 HO 分支 | e697af92bbca071b43bcaffc11efbb406a54620d831e592971c1bf3e0e8ae943 |
| [N7 rigid](JSP404_F18_T2_N7_RIGID_OCT7.md) | 七点 HM2 的 $h=5,6$ | 65847ee6287f8ff7ee8b867abb11076467e25d0f1b2685e8667bc9508588694e |
| [N7 pentagon](JSP404_F18_T2_N7_PENTAGON_OCT7.md) | 七点最后 HA+HM+LI3+$I2$；与前三份合并才是全部七点 | c6cf1fed9ff5319819475d90c78270ea193c73fcf6ad227e332c4dce5d377924 |
| [N8](JSP404_F18_T1_N8_OCT7.md) | 全 $t=1,N=8$；含 rigid 缩放、pure-LI block≥4 及实际 F16 负控 | 28a662654fd618485e7ee64db3499ac6d38ba924190c98aca9a4eb67a0fc3d97 |
| [N9](JSP404_F18_T0_N9_OCT7.md) | 最后 $I2/h7$ 与 $I1/h8$；低 hull 计数及 LB 排除是额外共享前提 | 63a7872749df92a0df9b04921305d034bef2e2865f94c69d375790b752dbfcd2 |

较早冻结稿列出的“尚未排除”是当时的 scope，后续 note 继续关闭；不能只读一份旧残余表便覆盖后续结果，也不能反过来把单份新 note 说成整个原题。

## 3. 已存在的 typed 接口及本次看到的证据

| 模块 / 接口 | 证据与限制 |
|---|---|
| ActualMinimalBandCounterexample.Model、actual_minimum_score_critical_form | 实际 minimum-card counter 与原最轻点零增益已有声明。单删 cap 来自 Model.minimum_card；没有无条件可删假设。 |
| ActualInteriorOneRuns | 冻结 source c8cf8f2bf189bc2c28506567f5518a24d7ad6b39f69b19a1992fd487945386db；[receipt](JSP404_ACTUAL_INTERIOR_ONE_RUNS_RECEIPT_20261007.json) 记录 final strict 与 genuine normal build、九个 selected exports 标准三公理。其 receipt 明确不含完整三 runs、exact singleton 或完整 F18 排除。 |
| actual_ordered_surrounding_bits、actual_interior_twisted_flip_count_ge_three | 从原实际含心三角形与实际排序射线生成 lift alternation；caller 不给 sign array 或 flip-count certificate。 |
| actual_interior_one_zero_gain_has_closer_point | 输出的是 $\operatorname{dist}(q,j)<\operatorname{dist}(q,p)$，common endpoint 为 target q；没有反向最近邻偷换。 |
| actual_low_four_F18_light_nearest_full_hull、exists_actual_low_four_F18_light_nearest_full_hull | 同一 c8cf source 的 selected checked exports；在真实 Model/F18 中内部生成 min-score-one 与原最近邻结论，包含 ties。 |
| ActualInteriorOneAngleGap | source f0b2c120fe28be5eed2f19b04d97f86d90cbd2242c3055e77bbad59a1adef39c；[receipt](JSP404_ACTUAL_INTERIOR_ONE_ANGLE_GAP_RECEIPT_20261007.json) SHA8853615e39e52162012690a6253de1d114717b62aee779e3ed6f5f5c93a8e873 已独立读到。actual_interior_one_angle_lt_twice_le_remainder 与 actual_interior_one_angle_gap 两个 exports final strict、genuine normal 均 PASS，标准三公理。它只完成 actual 标量二择，不完成三 classes。 |
| ConeDeletionProgress.exists_emitter_of_common_cone、not_common_cone_of_zero_incoming | source 6e09004a39012a02d5586785a5af0e9e91d74e6e060a4f3b67023d43068c1b53；[receipt](JSP404_CONE_DELETION_PROGRESS_RECEIPT_20261006.json) 记录 strict/normal 标准三公理。它要求实际有向 common cone；不自行从 fullHull/LB 产生 bisector。 |
| ActualRigidCardinality.legality_at_double_scale、card_le_four_of_actual_angle_gap | source 56ab23541ab6f7e422da750bd5fe762cf514d84a22dc50b2b0983881c02e1fec；[receipt](JSP404_ACTUAL_RIGID_CARDINALITY_RECEIPT_20261007.json) 记录 final strict 与 genuine normal、标准三公理。真实 angle-gap 仍是显式 premise，不自动替用户生成 interior/HM/HO 的刚性。 |
| ActualInteriorOneCardinality.selected_actual_interior_one_card_le_four | 源码已从原 selected actual interior score-one points 调用前两个 producer；integration 正独立检查。此 map 未见 final receipt，保持 pending，不提前计 PASS。 |
| SecondStrip.potential_le_four_of_second_strip_low | 现有 weighted actual n2 LOW capacity 声明。R4 的“全 $\mu$-score 零”要用这个 weighted bound，不仅是 rigid cardinality≤4。 |

这些是 scoped pieces。特别是现有 angle-gap 只给
$\angle\le R\lor2\lambda\le\angle$，不自行给 apex、class cardinality 或 exact deletion gain。

## 4. 需实现的共同实际 producer

下面的名称是建议声明名，不声称已存在或已 PASS。

### 0. ActualF18Frame

从原实际 Model 与 F18 接入上游实际排除，产生所有原行 $\kappa\in\{1,2\}$、heavy 均为原 fullHull 顶点、heavy 数 $t\le3$，以及

\[
L+2t=9,\qquad N=9-t.
\]

Min-score-one 已有 scoped checked Model consumer。Max-score-two 与 fullHull/heavy-count 的 actual producer 必须绑定上游独立证明，不能把 generic SAT 的不可满足性或希望得到的数值 profile 当作实际结论。

Heavy≤3 的纸面桥是：若有四个原 heavy，取它们及任意第五个**实际**点；删除单调使该真实五点子集 potential 至少十七，违反 actual GlobalFiveLow capacity 十六。这里子集的行可以增长，绝不把原凸包身份、Flat 或 $\kappa\le2$ 自动搬到子集。

### A. ActualInteriorOneClasses

输入必须是原实际 $c,\lambda$、Section4Legality、原 fullHull nonvertex p、原 rowScore 一，及非零 reference；不允许 caller 直接给抽象三类或希望得到的夹角。

内部产生所有 $j\ne p$ 的三个非空原索引类、完整 partition、实际方向 spans、唯一 apex，并证明：

\[
\begin{aligned}
&\text{总 span}\le R,\quad \text{同类角}\le R;\\
&\text{异类角}\ge2\lambda,\quad
 \text{apex--nonapex 角}\ge3\lambda;\\
&g_{pq}=1\iff q\text{ 是其类 singleton},\quad
 g_{pq}=0\text{ otherwise}.
\end{aligned}
\]

实现可复用已检查 actual window/lift producers：实际 gap 后 cut，选择实际射线作为 reference，在窄窗口内用 false-left / true / false-right 构造三类。True 类是 apex。要保留 actual chart invariance、完整 directionRow 与 deleteIndex 对接；不能只凭标量 angle-gap 定理命名三个 abstract runs。

### B. ActualFullHullConeTypes

从原 actual fullHull vertices 产生相邻 hull edges 与有向 cone，内部证明所有原 actual rays 在其中、内角 $\alpha$、外 gap $e=\pi-\alpha\ge\lambda$。

再从实际 gap score 推出：

| 类型 | 必须输出的实际事实 |
|---|---|
| HA | $\kappa2$，外 score2，$\alpha\le\pi-3\lambda<\pi/3$ |
| HM | $\kappa2$，外 score1，唯一内 big≥$2\lambda$；两端总宽≤R、跨端≥$2\lambda$ |
| HO | $\kappa2$，外 score0，唯一内 big≥$3\lambda$；两端总宽≤R、跨端≥$3\lambda$ |
| LB | $\kappa1$，外 score1，$e\ge2\lambda$、$\alpha\le\pi-2\lambda$ |
| LI | $\kappa1$，外 score0，唯一内 big≥$2\lambda$；两端总宽≤$T=\pi-3\lambda<\pi/3$，跨端≥$2\lambda$ |

原 fullHull 与任何 proper subset hull 始终分开。需要删除稳定性时，从实际 three-class singleton 及原零增益推出，不能作为默认公理。

### C. ActualHullExteriorBudget

内部建立原实际凸多边形 $\sum e_i=2\pi$。结合 $e_i\ge\lambda$ 及类型的基预算，推出

\[
K=h+2a+d+b\le8
\]

及 $h\le8$、$a\le2$。这里 a,d,b 是 HA、HM、LB 原 hull 顶点数。不能只接受 caller 提供 exterior-sum 数组。

### D. ActualF18DeletionLedger

从 actual Model、原 F18 与 minimum-card 定义，对任意原删集 D 且保留至少三点，证明 proper actual subset potential≤16，并得到

\[
\sum_{i\notin D}2^{\kappa_i}
 (2^{\kappa_i(P\setminus D)-\kappa_i(P)}-1)
\le\sum_{q\in D}2^{\kappa_q}-2.
\]

再内部生成 light 单删全零、heavy 单删预算2、所有保留 heavy 行单删全零、二删 light 不许 heavy score 增长。需要实际 subset 重编号与 Section4Legality.restrict_injective。

这不是说删除后的配置仍 critical。不能在一次删后重新使用原精确 debt；多删直接回到原 Model 的 proper-subset IH。

### E. Rigid Actual Restriction

Rigid 集是原 interior score1 与 HM/HO 原 hull 点。从 A/B 生成所有实际观察角的二择，重编号成实际 Fin 配置，使用已检查 ActualRigidCardinality。

R4 后续还需：

1. $\mu=2\lambda$ 的 weighted potential≤4；
2. 四项权重均≥1，故全部 $\mu$-score0；
3. $\pi-\mu<2\pi/3$ 排 rigid-subset interior；
4. 原角若≤R，外 gap≥$4\lambda=2\mu$，违 $\mu$-score0。

由此 rigid 四边形内角≥$2\lambda$、原 interior 其它 rigid 分居两个 nonapex。这里 rigid 子集的 hull 与原 fullHull 是不同对象。

### F. Shared derived consumers

这些可以在 A–E 之上做小模块，不应复制希望得到的最终容量作为 premise：

* light 不为 interior class singleton；每 heavy 至多一次收费2 singleton；
* HM/HO 每端至少两点，且真实半尺度 witness 排除它成为任何 actual point 最近邻；
* HA 最多承接一个 nearest target；hull light 最多两个；
* pure-LI block≥4：非空 $U$、$P\notin U$、U 全为原 LI hull light、在 P 与其余原点 cross≥$3\lambda$，结合原 light 零单删；
* 最小原半径二点 nonapex run 的严格双向 uniqueNN；
* 多删相应原 class 被清空时的实际 score 增长与原 interior 暴露。

## 5. LB scope bridge：不能隐去的 fullHull 步骤

N9 冻结 note 的 $h=7,I2$ 正文使用“所有 hull 点 LI”。仅曲率给 $b\le1$，不能单凭它写 b=0。

完整 paper 的额外排除是：若 light q 为 LB，原实际 cone 宽
$\alpha_q\le\pi-2\lambda$。取两个真实 hull 边界 rays 的 bisector u，$u\ne0$，所有 actual rays 都满足

\[
\operatorname{angle}(c_j-c_q,u)\le\alpha_q/2
\le\pi/2-\lambda.
\]

已 checked 的 ConeDeletionProgress.exists_emitter_of_common_cone 给某行向 q 的 gain≥1，违反原 light q 的全零单删。

**尚未 typed 的桥**是“fullHull/LB → 实际边界 rays → 非零 bisector → common oriented cone”。不能把已 checked 的 conditional cone theorem 当作已经提供了这个 producer。

### 可替代的 h7 bridge，允许至多一个 LB

这个新短证明不依赖 b=0，可直接补齐 N9 frozen note 的 scope：

1. 在 $h7,I2$，两个 interior X,Y 不可能把对方放 apex；此步只用每个 interior run≥2。
2. 它们的 apex U,V 都是 hull light、非空且至少两点、互不相交。
3. 大角传递把 V 放入 X 的含 Y nonapex；X 另一个 nonapex 位于 $W=HL\setminus(U\cup V)$，至少两点。因此 $|U|+|V|\le5$。
4. 曲率给最多一个 LB，而 U,V 不交，所以至少一个 apex 全为 LI。pure-LI block≥4 给该 apex 至少四点；另一 apex 至少两点，故 $|U|+|V|\ge6$，矛盾。

因此 h7 的全 LI 和 one-LB 情形都排除。若实现采用这个 bridge，可以不先实现全局 no-LB bisector consumer；但冻结 N9 长证明原有的 LI 前提仍应明确记录，不能改口说其仅凭曲率得到。

## 6. N9 只读独立审查结论

审查对象保持 SHA63a787…fcd2，不改文件。

* 两 interior 的最后模式，四个 small 角分别给
  $Xq<Xp$、$Xp<Yp$、$Yp<Yq$、$Yq<Xq$；严格短边循环方向正确。
* $|T_X\cap T_Y|=2$ 的子分支，两个 large 角分别位于 X 与 z，small 位于 p；没有角中心交换。
* 一 interior 的选择点 w 只要求在两个 nonapex runs 中半径最小，允许并列。
* 反向 uniqueNN 的余弦差恒等式正确：

\[
w'v^2-d^2=(r_v-r_w)(r_v+r_w-2r_{w'}\cos\theta')
 +2r_{w'}r_w(\cos\delta-\cos\theta').
\]

  $r_v\ge r_w$、$r_{w'}<2r_w$、$\cos\theta'<1/2$ 给第一项非负；$0\le\delta\le R<2\lambda\le\theta'\le\pi$ 给第二项严格正。无需假定余弦为正。
* w 对所有原九点候选严格更近于 w'，w' 对所有原九点候选严格更近于 w；这是真双向 uniqueNN，不是单向结论或仅子集最近邻。
* mutual pair 在第三中心角≤$\pi/3$，故不能跨 LI clumps；最后另一 clump singleton 违反的是原零 light 单删，未套中间配置 debt。
* “z 不在 apex U”在角传递公式中必须指 U 外的原 hull 点，不包含中心 X；实现声明应显式写索引不等式。

除上述需显式补明的 LB producer 外，没有发现三角方向、strict cycle、uniqueNN 或 ties 的逻辑错误。

## 7. 全分支覆盖与建议实现顺序

| heavy 数 t | 点数 N | paper 覆盖路径 |
|---:|---:|---|
| 3 | 6 | mixed note 的 h3/h4/h5/h6；heavy HM 四边形 singleton matching 是实际几何，不是 subset SAT |
| 2 | 7 | h3 若有 hull light，light 删除稳定性/nearest 容量排；h4 由独立 N7 note；h5/h6/h7 由 HO、rigid、pentagon 三 notes |
| 1 | 8 | N8 的 R4/R3、小 hull 及 curvature，剩 HM/HA/HO 三模式分别由 pure-LI block 和 apex partition 排除 |
| 0 | 9 | I≥5 由 rigidcard；I4 R4；I3 R3；I2 冻结长证明加 LB bridge或本map短桥；I1 冻结严格 mutualNN；I0 h9 由 curvature |

建议先实现 A/B/C/D 的原实际 certificates，再实现 F 的共用小 consumers，最后按 $t=3,2,1,0$ 接最终 Model contradiction。E 的 card≤4 consumer 与 actual interior angle-gap producer 已 checked，但 HM/HO 的实际 gap producer、selected subset consumer 的检查及 R4 geometry 不应跳过。

未来 top-level 目标可以命名 actual_low_four_F18_model_false；在接好所有实际生产者并完成 exact-source strict/normal 检查以前，这只是建议声明名，不是已有 theorem。

最终还必须与 F17 等其它原 counter 分支连接，才可讨论 n4 LOW 总容量；本 map 没有完成那个步骤，更没有宣布完整原题已解。
