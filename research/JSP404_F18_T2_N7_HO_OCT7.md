# F18：七点两 heavy 的全部 HO 分支排除

日期：2026-10-07。状态：actual 纸面证明；没有 Lean PASS、编译、Git 操作。接续冻结稿 [mixed hull](JSP404_F18_MIXED_HULL_OCT6B.md) 与 [七点四凸包顶点](JSP404_F18_T2_N7_OCT7.md)，不改这两份冻结文件。

## 1. 原配置事实与严格最近邻隔离

固定 minimal actual F18 counter，$2\pi/9<\lambda\le\pi/4$，$R=\pi-4\lambda<\lambda/2$。本 note 只处理 $t=2,N=7,L=5$。

每个 light 单删预算为零，heavy 单删预算为 $2$；任一保留 heavy 行 gain $1$ 收费 $4$，所以所有 heavy 行对任意单删均为零增益。直接删除两个原 light 的 proper actual subset 累计预算为 $2$。不把中间配置重新当 critical。

HM/HO 的实际两端簇总宽至多 $R$。两端均不能 singleton：清掉一个端点会合并外 gap 与内 big gap，合并长度至少 $4\lambda$，heavy 行增长至少 $1$。因此每个 target 都有同簇 witness，角至多 $R<\lambda/2$，给严格距离比较，HM/HO 不能成为任何 actual point 的最近邻。

若 $B$ 是 HO，跨其端簇的实际夹角至少 $3\lambda>\pi/2$。跨簇点 $U,V$ 满足 $UV>BU,BV$。同簇 witness 又给 $UJ<BU$。因此 $U$ 的最近邻严格留在自己端簇；这个结论同时使用 witness 排除中心 $B$，不能只用跨簇距离。

若 HO 的一个整端簇恰由两个 light 组成，直接删除这两点会使 heavy 行增长至少 $1$、收费至少 $4>2$，不可能。此处不要求两 light 先被证明 mutual。

## 2. Rigid 点的同端引理

称原 interior $\kappa=1$ 点及原 nonacute heavy（HM/HO）为 rigid。任一 rigid 中心观察两个其他点，其实际夹角要么至多 $R$、要么至少 $2\lambda$。

固定 HO $B$。若两个 rigid 点 $U,V$ 在 $B$ 的异端簇，三角形 $BUV$ 在 $B$ 的角至少 $3\lambda$。其余两角若任一个至少 $2\lambda$，两角和至少 $5\lambda>\pi$；否则两角均至多 $R$，和至多 $2R<\lambda$，迫 $B$ 角超过 $\pi-\lambda$。两种均非法。

所以所有 rigid 点在 HO $B$ 的同一端簇。该引理是实际角度结论，没有使用弱模型。

## 3. 七点中 HO 不能与 interior light 共存

设 $B$ 是 HO、$X$ 是任意原 interior light。令 $T$ 为 $B$ 的不含 $X$ 的端簇，记 $k=|T|$。第 1 节给 $k\ge2$。

对每个 $V\in T$，$\angle XBV\ge3\lambda$。若在 $X$ 行 $B,V$ 异 run，另有 $\angle BXV\ge2\lambda$，两个角之和至少 $5\lambda>\pi$。故所有 $\{B\}\cup T$ 在 $X$ 的同一 run，该 run 至少 $k+1\ge3$ 条射线。

$X$ 总共六条射线，另两 runs 合计至多三条。原 light 不能 run singleton，且除了 $B$ 以外只剩一个 heavy $C$。如果 $C$ 位于上述大 run，另两 runs 至少需要四个 light 点，不可能；如果 $C$ 不在大 run，另两 runs 至少需要 heavy singleton 加 light 二点 run，共三条。

因此唯一计数可能是 $k=2$、大 run 恰三条、$C$ 是其余 run singleton。特别是 $C\notin T$，所以 $T$ 恰由两个 light 组成。这违反第 1 节的直接二删预算。

故 **七点两 heavy 的任何 HO 与任何 interior light 都不能共存**。此结论不区分另一个 heavy 是 HA、HM 或 HO，也不区分 fullHull 大小。

这一次性排除了所有有 interior 的 HO 子域，包括 $h=5$ 的 HA+HO 及 nonacute+HO、以及 $h=6$ 的 HA+HO 和 nonacute+HO。原凸包与删除后凸包没有被默认相同。

## 4. 全部七点在 fullHull 的 HO 分支

此时 $h=7,\ell=5,I=0$。转角离散预算

\[
h+2a+d+b\le8
\]

迫 $a=0$，且至少一个 heavy 是 HO，记为 $B$；另一个 heavy $C$ 为 HM 或 HO。全部 heavy 都不能成为任何点的最近邻，light 最近邻只能是另外的 hull light。

HO $B$ 每个端簇至少含两个 hull light：若没有 hull light，端簇最多含另一个 heavy $C$、违反非 singleton；若只有一个 hull light，它的同簇其他候选只有 nonacute heavy，无法选择最近邻。

五个 hull light 因此按 $2+3$ 分到两端。若 $C$ 在三 light 端，另一端恰两个 light，直接二删清端违预算。所以重命名后

\[
B:\quad \{C,Q,R\}\mid\{S,T,U\}.
\]

中心 $C$ 不能成为最近邻，最近邻又不跨 $B$ 簇，故 $Q\leftrightarrow R$。

在 $C$ 的两端簇，mutual pair $Q,R$ 必同端，因为 mutual pair 在任第三点角至多 $\pi/3<2\lambda$。该端不能恰为 $\{Q,R\}$，否则直接二删又清空 heavy 端簇。

该端也不能含 $B$：若含 $B$，在三角形 $QBC$ 的 $B,C$ 两角都至多 $R$，迫第三角超过 $\pi-\lambda$。

因此 $C$ 的含 $Q,R$ 端簇必须加入某点 $V\in\{S,T,U\}$，且不含 $B$。于是

\[
\angle CBV\ge3\lambda,\qquad
\angle BCV\ge2\lambda,
\]

两角和至少 $5\lambda>\pi$，矛盾。无需假定 $C$ 的端簇是 $3/3$；$4/2$ 情况同样包含上述点 $V$，已被排除。

## 5. 更新后的最小剩余

结合七点四凸包顶点证明，**所有 $N=7,t=2$ 含 HO 的配置都已纸面排除**。七点仍未闭合的模式仅有：

| fullHull 大小 | 原满凸包类型 | interior light 数 |
|---:|---|---:|
| 5 | HA + HM + LI3 | 2 |
| 5 | HM2 + LB$^b$ + LI$^{3-b}$，$b\in\{0,1\}$ | 2 |
| 6 | HM2 + LI4 | 1 |

此表是实际 counter 的必要剩余，不宣称这些整数模式可实际实现。$t=0,1$ 的八点、九点分支仍未闭合。本 note 不把纸面子域排除写成 Lean 完成，也未重复套用中间点集的原 critical debt。
