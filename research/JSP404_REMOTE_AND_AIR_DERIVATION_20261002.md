# JSP-000404 远端审计与 AIR 全题闭合路线

审计日期：2026-10-02（Asia/Shanghai）。结论：完整原题仍未证明。本文件给出可核验的归约、已完成子域、实质缺口及实现顺序；不声称这些 OPEN 几何引理已有证明。

## 1. 全部分支与提交

已抓取 `origin` 全部 28 个分支。主干为 `lane/integration@c2b4c9931385bc9a65ce022ae73533b5c8845e4c`。完整 40 位 HEAD、日期、相对主干的全部独有提交清单在 [REMOTE_SNAPSHOT](JSP404_REMOTE_SNAPSHOT_20261002.json)。以下不是工作进程状态：分支名包含 active/owner 并不能证明任务仍在运行。

| 分支 | HEAD | 相对主干 |
|---|---|---|
| agent/jsp404-air-emergency-owner-20260928 | `0c49a82beb02` | 独有 34 / 主干独有 3 |
| agent/jsp404-angle-cert-goal-01-owner | `9ae823086d0a` | 独有 23 / 主干独有 112 |
| agent/jsp404-closed-to-strict-01-air | `2f0d4f913c0a` | 已被主干包含 |
| agent/jsp404-competitor-crossmap-01-challenger | `b3342399d49e` | 已被主干包含 |
| agent/jsp404-g3-merge-candidate | `83d3dcf4b7e9` | 独有 3 / 主干独有 43 |
| agent/jsp404-geometry-skeleton-bridge-01-owner | `0889f5d4ac3e` | 已被主干包含 |
| agent/jsp404-l2-l3-strict-01-owner | `6d16ebe714ac` | 独有 3 / 主干独有 108 |
| agent/jsp404-maxgap-emission-01-owner | `4563dc091eb0` | 已被主干包含 |
| agent/jsp404-maxgap-emission-02-spec-audit | `79e25b1c8206` | 已被主干包含 |
| agent/jsp404-proof-convergence-02-owner | `4542b78e50a6` | 已被主干包含 |
| goal/jsp404-completion | `0ceac4df4018` | 已被主干包含 |
| lane/a-low | `d5b2f035e14d` | 已被主干包含 |
| lane/a2-lowclose | `4bf55d39754b` | 已被主干包含 |
| lane/a3-low-admissible | `3093688bf6ba` | 独有 1 / 主干独有 93 |
| lane/b-high | `87eb7990f2e6` | 已被主干包含 |
| lane/b2-highmech | `3e8d58aadd75` | 已被主干包含 |
| lane/b3-allbad | `22b856632888` | 已被主干包含 |
| lane/c-gadget | `4dd5282b9fa2` | 已被主干包含 |
| lane/d-integration | `ddd615107cd6` | 已被主干包含 |
| lane/e-challenger | `aa6ebb55f07d` | 已被主干包含 |
| lane/e2-challenger | `4fe7037b332c` | 已被主干包含 |
| lane/h-general-high | `f4ec31e97912` | 独有 1 / 主干独有 93 |
| lane/integration | `c2b4c9931385` | 已被主干包含 |
| lane/l1-lowp | `2e19fd3f57ab` | 独有 1 / 主干独有 88 |
| lane/v1-vacuum | `1e35549f46fe` | 独有 2 / 主干独有 88 |
| lead/jsp404-wave2-integration | `3da4fb80c2be` | 独有 1 / 主干独有 96 |
| lead/jsp404-wave2-integration-v2 | `567c3d3349aa` | 独有 1 / 主干独有 93 |
| master | `652ed02f86ed` | 已被主干包含 |

主干相对上次 `12775cd` 只有对手研究记录更新。主要新代码在 AIR 分支。审计起点为 `116bb65b57e158ebdd3bb854f0b33079e9e01c83`（31条主干未包含提交）；审计过程中又推送了 `366a120`、`a6de321`、`0c49a82`，最新 HEAD 为 `0c49a82beb0291f7f7c02206cf7d1e259dc2979e`（34条）。主干独有的 3 条均为对手研究文档；`git merge-tree --write-tree` 的试合并无冲突，旧116bb65输出树 `82dae9e5644c314b6b4b04492397d05c1b04782e`；最新0c49a82试合并也无冲突，输出树 `bbc7b594c3eb08a992721341894131467901abcd`。没有实际移动主干或 AIR 工作分支。

AIR 工作目录现场另有未提交的 `FivePointCapacity.lean`、`MixedStarExclusion.lean` 修改。旧固定版本已隔离重建；新推送把相关工作提交了，最新固定源码亦已单独追加审计，未覆盖工作区。

关键新提交：

- `06b9a3a`：R3 三类 pairkill，48 个传递性分支。
- `549bed8`、`b10c330`、`2bd9f4d`：五中心 R3/R4 闭合。
- `429e876`：五中心闭合接回实际容量接口。
- `8ada8a5`：任意规模的 defect-2 行数至多 2。
- `f5670db`、`b5d1e4a`：两个低缺陷行的位置分类与尾部 defect≥3。
- `606188e`：删两行的容量消费者。
- `4d240e5`、`86e9ef3`：加权 slack 与占箱约束接口。
- `90b88c3`：删锚点晋升与极端接收点 clump 子域。
- `e98081f`、`9732709`：BETWEEN 剩余情形的短弦/顶部聚簇分解。
- `55700f3`：实际最大 θ 走廊关闭 top-clump；BETWEEN 剩余时供给到尾点的短弦。
- `116bb65`：相关账本更新。
- `366a120`：R2短弦存在性取消BETWEEN前提、任意尾点删除保留R2、尾权账本与二进制最小超额。
- `a6de321`、`0c49a82`：上述进度及远端HEAD记录。

`proof-convergence-02-owner@4542b78` 已包含在主干。G3 候选 `83d3dcf` 只审了更早一批，不能作为最新 AIR 提交的验收。A3 与 H-general 最新独有提交仅是任务规格。L1 仍是约 17000/85536 的未完扫描；V1 修正了将 W=5/2 边界误报成 W>5/2 的记录，未给出通用 HIGH 容量证明。

## 2. 统一数学记号

对真实中心 c_i 的每行无向方向（模 π）排序，间隙 g_ij 非负且和为 π。令

\[
 n=\lfloor\pi/\lambda\rfloor,\quad
 \delta=\pi/\lambda-n,\quad
 k_i=\sum_j\max(\lfloor g_{ij}/\lambda\rfloor-1,0).
\]

设几何缺陷 `c_i=rowDefect_i=n-k_i`，饱和行为 c_i=1。旧 skeleton 记号则是 d_i=c_i−1。故

\[
 F=\sum_i2^{k_i}=2^nK,\qquad
 K=\sum_i2^{-c_i},\qquad W=2K=F/2^{n-1}.
\]

不要把 d 和 c 混用：会把目标常数错开一倍。真实行满足 1≤c_i≤n；以上实指数等式是在这一实际几何域内使用。

LOW：0≤δ<1/2，目标 F≤2^n（K≤1、W≤2）。等价 λ 区间为 2π/(2n+1)<λ≤π/n。

HIGH：1/2≤δ<1，目标 F≤2^n+2^(n−2)（K≤5/4、W≤5/2）。等价 π/(n+1)<λ≤2π/(2n+1)。接口的 HIGH 上界对整个 δ<1 都需成立；LOW 区间可复用更强的 LOW 上界。

共同几何域必须固定 e≠0、n≥3、s≥3、0<λ<π、floor(π/λ)=n、`Section4Legality c λ`；不能用 free n/big 替代实际带区间绑定。

## 3. 已关闭与仍 OPEN 的精确子域

已证：所有 N≥3 的 sharp 上界构造；普通点集 N=3…8 的完整值；n=1,2 的容量；任意规模 LOW 有饱和中心；任意规模 HIGH 有两个饱和中心。

最新 AIR 另证明：n≥3、真实中心总数 3≤s≤5 的 HIGH 容量，及唯一饱和锚点时 defect-2 非锚行数 r≤2。这里 s 是中心数，不是普通点集原题中的 N，不能混淆。

因此任意规模还缺：

| 子域 | 精确缺口 |
|---|---|
| LOW，无饱和行 | n≥3、s≥5、δ<1/2，证明 F≤2^n |
| HIGH，无饱和行 | n≥3、s≥6，证明 F≤5·2^(n−2) |
| HIGH，恰一饱和行 | 任意长尾部的精确预算，见下节 |

主干 `MainTheorem.sendov_lower` 在 N≥9 仍有 `sorry`。`GeometricCertificates` 与 `SelectionP` 仍是条件消费者，不是已证的全题定理。

## 4. 唯一饱和 HIGH：完整的算术归约

记 Q=2^(n−2)，锚点贡献 2Q，r 个 defect-2 行各贡献 Q，T 中所有尾行 defect≥3。已证 r∈{0,1,2}，所以

\[
 F=2Q+rQ+\sum_{i\in T}2^{n-c_i}.
\]

完整目标严格等价于

\[
 \boxed{\sum_{i\in T}2^{n-c_i}\le(3-r)Q.}
\]

每个尾行的贡献≤Q/2。因此 |T|≤2(3−r) 时直接闭合；三个第一剩余规模分别是 r=2 时 s≥6，r=1 时 s≥7，r=0 时 s≥8。这个结论可由有限和及幂单调性证明，不需要枚举配置。对应算术源码在 [DERIVED_ARITHMETIC](JSP404_DERIVED_ARITHMETIC_20261002.lean)，已在 Lean 4.34.0 下以 --trust=0 核验，所列定理仅依赖标准公理。

对于 r=2，实际 θ 排序将尾点位置归为 ALL_BELOW、BETWEEN、ALL_ABOVE。最新 `r2_residual_tail_emission` 已把 ALL_BELOW、BETWEEN、ALL_ABOVE 三域统一：任意超容量R2域都供给 **短弦到尾点**。它仍不是权重预算，也不是删点正增益。无需再分别证明三个位置类的短弦存在性。

### 已证的 top-clump 论证为何成立

置 β=π−nλ<λ，选 θ 最大的端点 b，令 U=θ_b+π−λ。defect=2、两端均为大间隙、末端 floor=1 强制首端 floor=n−1，因此该行的全部弦被夹在 [U−β,U]。

取

\[
 w=((n-2)\lambda+2\beta)/n,\qquad S=\lambda+\theta_b-\beta.
\]

则

\[
 w-\beta=(n-2)(\lambda-\beta)/n>0,\quad
 \lambda-w=2(\lambda-\beta)/n>0,
\]

且 0<S≤λ、S+nw=U<π。实际几何使每根弦位于 [λ,U]；每行右侧预算 θ_i+π−U=λ+θ_i−θ_b≤λ。聚簇宽度 β<w，因而该 defect-2 行占一个箱，其 slack 为 2^(n−1)−2^(n−2)=Q，恰好足以调用 `potential_le_high_of_saturated_slack_sum_start`。旧 θ_b≤2β−λ 阻塞只是更宽走廊的产物，已被新证明消除。

### 下一条几何引理应供给什么

在同一有效网格中，令 a_i 为占箱数，C_i=2^(n−a_i)，w_i=2^(n−c_i)。已有 a_i≤c_i，从而 C_i−w_i≥0。若能从实际几何独立构造一族行 T_0，满足 Σ_{T_0}(C_i−w_i)≥Q，现有 slack 消费者即可闭合 HIGH。

一个真实、非同义改写的充分构造是：证明存在两个不同尾行，在 **同一有效网格** 中都占至多两箱。因为 c_i≥3，每行 C_i−w_i≥Q−Q/2=Q/2；两行可供给 Q。该供给的通用几何存在性尚未证明，不应加成新假设后宣布完成。

有洞并不够。n=3 的抽象不相交子立方体 00*、01*、100、101、110 具有 occ=defect=(2,2,3,3,3)，尾侧权重7、洞1、slack0，加锚点4 得 F=11>10。这个 exact 负控只否定“上述抽象计数条件足够”的路线，未声称存在相应合法平面配置。

## 5. 可加强的主线：最小反例、最轻行与终端约束

删点 v 的真实增益 g_iv≥0，精确恒等式为

\[
 F(C-v)=F(C)-w_v+\sum_{i\ne v}w_i(2^{g_{iv}}-1).
\]

若存在 v 使右侧增益和≥w_v，删点不降低 F，再按中心数 s 强归纳。前提必须是 **超容量**；合法但未超容量的方形及三角形加中心已否定无条件删除规则。

在最小中心数的超容量反例中，每次删除的配置已被归纳假设压到 cap 以下，故

\[
 0<F-cap\le w_v-\sum_{i\ne v}w_i(2^{g_{iv}}-1)\le w_v.
\]

令 w_min=2^kmin 为最小行权重。所有 w_i 和 cap 都被 w_min 整除，因此正超额 F−cap 是 w_min 的正倍数。选择最轻 v 得

\[
 \boxed{F=cap+w_{min}},\qquad
 \boxed{\sum_{i\ne v}w_i(2^{g_{iv}}-1)=0}.
\]

因各项非负且权重为正，该最轻 v 在所有其他行中引起的真实增益均为零。这是增加到几何搜索中的严格约束，可把“找任意 witness”改成“排除实际合法的最轻零增益终端”。它仍未给出终端不可能性的通用证明。

实际操作：先在 r=2 的三个 θ 位置类中研究这一额外条件，证明它强制足量 slack，或强制两个真实供血点、或与三角传递性矛盾；然后覆盖 r=1、0 和无饱和两域。证明失败时记录具体尚缺的几何命题，不能把它藏进容量假设。

新短弦不能充当上述增益：`DeletionRigidity.deletion_rigidity` 保持两个 defect-2 行在删任意第三尾点后的分数，因此对应 low→deleted-tail 的 g 恰为零。若试图反向使用，需重新证明 tail→deleted-low 的 gain；即便它为1，defect-3 尾行只贡献 Q/2，仍不足支付一个 Q 的 low 行。


### 0c49a82 新增的 R2 闭包与正常形

`r2_tail_delete_closed` 已证明删任意尾点保留R2类型，故可以在R2内部按中心数归纳，而不假定尚未证明的所有HIGH域。
令 L_T=Σ_tail w_i（不是旧 skeleton 的 W），u=min_tail w_i。最小反例中每个实际删尾配置满足 L_T^−(q)≤Q，且

\[
 L_T^-(q)+w_q=L_T+G_q.
\]

由此 G_q+(L_T−Q)≤w_q；二进制整除再给出 L_T=Q+u、F=5Q+u。每个最小权重尾点 q 有 G_q=0，删后的尾质量恰为Q。

目前 normal-form 定理源码的 g:ι→ℕ 在所有 q 中共用，而实际增益 g(q,i) 随被删点变化。可改成双参数矩阵；也可合法地以g=0实例化，利用原删后权重≤实际删后权重先取得 L_T=Q+u，再单独代入真实 q 的账本取得 G_q=0。配置层实例化仍应单独实现和核验。

**G6里程碑有精确适用域。** n=3时所有尾行3≤c_i≤n都等于3，w_i=u=1且Q=2；L_T=Q+u=3强制只有三个尾点，总共6中心。证明 `(1,2,2,3,3,3)` 的最轻零增益实际几何不可能，就能关闭整个n=3的任意规模R2。

这不关闭任意n。即使只有6中心，纯算术也允许 `(1,2,2,3,3,c)`，c≥3。n=5、Q=8，尾权(4,4,1)产生F=41=5Q+1，满足最小超额。这不是平面反例，只否定从算术直接归约到三个相同defect-3尾点。n≥4还需要额外几何压缩/刚性/加权供血定理。

此外，通用短弦定理返回某个尾接收点，未保证它的权重最小。最小超额仅保证删最轻点零增益；较重接收点仍允许 0<G_q≤w_q−u。不得把两次存在量词的见证擅自认成同一点。


### n=3 全部缺口还能进一步归为16个数值轮廓

这是最小反例正常形的纸面算术推论及精确枚举，不是相应平面配置不可能性的证明。n=3时权重只有4、2、1。令 a_j 为 defect=j 的行数。

- LOW0（cap=8）：有weight1时 F=9，2a_2+a_3=9，a_2=0…4；没有weight1时 F=10，a_2=5。共6轮廓，中心数5…9。
- HIGH0（cap=10）：有weight1时 F=11，2a_2+a_3=11，a_2=0…5；没有weight1时 F=12，a_2=6。共7轮廓，中心数6…11。
- HIGH1：a_1=1，a_2=r∈{0,1,2}，F=11强制a_3=7−2r。共3轮廓，总中心数8、7、6。

具体列表见 [N3_CRITICAL_PROFILES](JSP404_N3_CRITICAL_PROFILES_20261002.json)。完整证明这16个必要轮廓在真实几何及最轻零增益约束下都不可能，可关闭整个n=3容量、进而把普通原题扩展到N≤16。仅证明G6不能代替其余15个轮廓；全部n=3也不能代替n≥4。

## 6. 无饱和域的统一方向切割候选

这是可形式化的归约，**切割选择定理仍 OPEN**。

将方向圆分成 n 个宽 λ 的主箱与宽 ρ=δλ 的残余箱。对任意有限配置，先选不落在方向/箱边界事件上的 generic cut；δ=0 必须另证边界版本。箱内实际角宽严格小于 λ，所以合法性排除同一顶点在一箱中同时为入点和出点，得到二分图与 source/sink 位。

主箱位定义每行的布尔子立方体 Q_v，空位数 e_v，|Q_v|=2^e_v。两个 Q_v 相交时对应边只能在残余箱；残余图二分意味着每个码字最多覆盖两次。记 U 未覆盖数，O 双覆盖数。循环空箱计数给出

\[
 k_v\le e_v+\mathbf1_{\{v\text{没有残余边}\}}.
\]

对 k_v=e_v+1 的缺损行记 D=Σ|Q_v|；其子立方体与所有其他行不交。其余行记 S=Σ(|Q_v|−2^kv)≥0。精确恒等式

\[
 F=2^n-U+O+D-S.
\]

因此若能证明每个实际合法配置 **存在** 一次切割，在 LOW 使 O+D=0，在 HIGH 使 O+D≤2^(n−2)，两个无饱和域一起关闭。已有 `bipartite_cover_weighted_bound` 消费最终编码；循环计数、边界情形和这条选择存在性需要 AIR 证明。

不要改为 O+D≤U+S 后当作新进展，它是原容量不等式的等价改写。不要强求一个全局空残余区间，严格合法 LOW 整数五边形已经给出反例。不要用一次切割或随机样本成功代替存在性证明。可枚举有限旋转事件区间，但须有证明保证至少一个区间满足预算。

## 7. 为什么三条容量界真的能关闭完整原题

用已证的实例化与计数桥即可由容量得到任意普通点集 |C|≤cap。也可直接观察普通点集的每个权重2^kv≥1，故 N≤F。

设 2^k<N≤2^(k+1)。假设所有实际三点角均小于 α_N，取有限最大角 A 并设 λ=π−A，则 λ>π−α_N。

- 第一档 N≤2^k+2^(k−2)：α_N=π(1−2/(2k+1))，故 π/λ<k+1/2。当 floor(π/λ)=k 时 LOW 容量给 N≤2^k，与 N>2^k 矛盾；更低的 floor 带使用其更小的容量。
- 第二档 N>2^k+2^(k−2)：α_N=π(1−1/(k+1))，故 π/λ<k+1，HIGH 容量给 N≤2^k+2^(k−2)，同样矛盾。

例：N=9 需要 T<3.5 时 F≤8；N=11 需要 T<4 时 F≤10。已有消费者处理所有 floor/ceil、小 N 和角的点成员/不相等条件，不必重复重写。

容量可先直接证明，再令 `GeometricCertificates` 的超容量域为空，由 False 消去它要求的 dichotomy；继续调用 `gadgetSelection_of_geometricCertificates`、`sendov_lower_of_selection`、`sendov_alpha_eq_of_selection`。这避免把较强的证书形状当必须的路径。

sharp 上界已证，最终将上述下界与任意 ε>0 的上界构造配对即可得到真正极值量与 alphaN 的相等。不要用 α(N(a))=a 这种阶梯函数互逆等式。


### 原题更弱、范围仍完整的替代目标：两族跳点

不要把更强的全局加权容量误当作原题唯一必要任务。已有任意N的上界时，只需证明下列两族**普通点集下界**（全部n≥2）：

\[
 N_L(n)=2^n+1:\quad \max\angle\ge\pi(1-2/(2n+1));
\]
\[
 N_H(n)=2^n+2^{n-2}+1:\quad\max\angle\ge\pi(1-1/(n+1)).
\]

理由是每一档中 alphaN 恒定。任何更大的配置都可取前N_L或N_H个互异点构成真实子配置；子配置给出的同一个三点角仍在原配置中。`lower_bound_mono_by_take` 已实现这种保持成员、不相等和角下界的传递。n=2两个跳点5、6已有下界；n=3只需普通点集9、11两处新的下界；n=4是17、21。N=3、4由现有小规模证明处理。

两族对所有n的证明是一个**完整原题目标**，不是有限特例。它们仍未证明，不能假设为新公理。AIR若找到原题直接几何证明，可经这条较弱路线完成，无须额外证明比原题更强的每中心加权容量。条件消费者/子配置传递本身不是新的跳点下界。

## 8. 文献、对手与边界提醒

对手仅 main，HEAD仍为 `3182c9b1d2b4e3f1ab2a98a64cfaabba2d72cda7`。他给出 N=3…8 及所有 dyadic N=2^k 的等值和全体上界，没有非 dyadic 完整下界；`SendovClaim` 仍只是定义。归档内118个清单项校验通过；日志标准公理、2599任务 build 成功是对手记录，未由本次重新构建。未发现开源许可证，不能假定可直接复制其代码。

原论文：俄文 [Sendov 1995](https://www.mathnet.ru/eng/fpm81)，Lemma4.10/4.11 的局部替换保持相同中心，没有把任意 s 降到5。Lemma4.12 pp510–512 的一般 s 最大指数列含 n−s+1，未说明 s>n+1 的非负修正；英文对应 [卷69文章 pp27–46](https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf) 同样不能当作已证明的任意规模最大轮廓定理。此处指出缺少可用的论证，不据此宣称最终 Sendov 公式为假。

修正文档：PentagonPacking 的无饱和反例 δ=3/4，只否定不分带的 K≤1，并不否定 LOW δ<1/2 目标；GeomSkeleton 的实际桥已经证明，缺的是全局 selection/capacity；严格余量标准化能增大 W、改变缺陷和饱和类型，只有全域容量可直接回传。

## 9. 交付和验收

复用固定的本地 Mathlib 产物，不能混入 AIR 工作区未提交证明。本次主干 `lake build` 已通过9007任务。root audit 需额外先 build 未在默认根里导入的 IntegrationCounterexample；绿色默认 build 本身没有运行这份审计。

完整结果必须有：原题类型不变的无条件 sendov_lower 和实际 α=alphaN；它们的传递公理仅标准三项，无 sorryAx；完整源版本、真实构建与复核记录；若走容量路线，δ=0、1/2与所有n/s均须覆盖；若走跳点路线，两族须对全部n≥2成立；两条路线最终都须覆盖所有普通N≥3。研究任务不得以通用几何存在性仍作为 premise 的消费者宣布完成。

AIR可直接执行的单份任务书：[AIR_TASK](JSP404_AIR_TASK_20261002.md)（3549字符）。

主干 root audit 已在补建 IntegrationCounterexample 后以 --trust=0 实跑 exit0；下界打印仍含 sorryAx。新的必要公理检查脚本实跑 exit1 并明确报告该 sorryAx，证明 completion gate 会拒绝当前部分证明。

最新固定 AIR HEAD `0c49a82beb0291f7f7c02206cf7d1e259dc2979e` 已在隔离源码中重新 build，通过9010任务；1399个跟踪文件逐项Git blob比对无差异。依赖缓存复用本地固定版本，不声称全新机器重建或独立人工数学审查。

最新AIR七项关键定理的单独公理审计已通过，仅标准三项。完整回执：[VERIFICATION_RECEIPT](JSP404_VERIFICATION_RECEIPT_20261002.json)。n=3的16轮廓配置层需共同强归纳，或先HIGH1后HIGH0；LOW0删点可进入已证饱和LOW。

子配置传递 `lower_bound_mono_by_take` 已与算术后端一同以 --trust=0 核验通过，公理仅标准三项；两族跳点的下界本身仍OPEN。
