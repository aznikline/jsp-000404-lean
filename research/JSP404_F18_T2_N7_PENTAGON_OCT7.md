# F18：七点 HA+HM 五顶点 fullHull 的实际 run 排除

日期：2026-10-07。状态：实际配置的纸面证明；没有 Lean PASS 或构建结论。

本 note 只排除 $t=2,N=7$ 的最后一个 HA+HM 五顶点分支。结合已经冻结的 [四顶点七点证明](JSP404_F18_T2_N7_OCT7.md)、[七点全部 HO 排除](JSP404_F18_T2_N7_HO_OCT7.md) 与 [七点 HM2 rigid 排除](JSP404_F18_T2_N7_RIGID_OCT7.md)，才得到全部 $t=2,N=7$ 分支的纸面闭合；本 note 单独不承担全部七点分类。$t=0,1$ 的剩余分支仍未闭合。

## 1. 原配置与使用的事实

固定 minimal actual F18 counter，参数满足

\[
\frac{2\pi}{9}<\lambda\le\frac{\pi}{4},
\qquad R=\pi-4\lambda<\frac{\lambda}{2}.
\]

特别地，

\[
0\le R,\qquad 2R<\lambda,\qquad 3R<\pi,
\qquad 5\lambda>\pi,\qquad 6\lambda>\pi.
\]

原七点集为

\[
\{A,B,Q_1,Q_2,Q_3,X,Y\}.
\]

原 fullHull 是五边形，其顶点恰为 HA heavy $A$、HM heavy $B$ 及三个 LI hull light $Q_1,Q_2,Q_3$；$X,Y$ 是原 interior light。使用下标避免把某个 hull light 与宽度参数 $R$ 混淆。记

\[
H=\{Q_1,Q_2,Q_3\},\qquad D=\{A\}\cup H.
\]

以下 fullHull 身份、实际方向 runs、端簇和 singleton 都指原七点配置。原配置没有三点共线，每个实际三角形角均不超过 $\pi-\lambda$。

证明只使用下列原 single-delete debt/run 事实。

1. 在 $B$，另外六点的射线恰分为两个实际端簇。总宽至多 $R$；同簇角至多 $R$，异簇角至少 $2\lambda$。每个端簇至少含两条射线：原 heavy 行对任意单删均无增益，而删空一个 singleton 端簇会使该 heavy 行增长。
2. 在每个 $P\in\{X,Y\}$，另外六点的射线恰分为三个非空实际 runs，总宽至多 $R$。同 run 角至多 $R$，异 run 角至少 $2\lambda$。其中有一个 distinguished apex run；它与任一个另外的 run 之间，所有实际夹角至少 $3\lambda$。
3. 原 light 射线在 interior 行不能成为 run singleton。这来自 light 单删总增益为零。因而在 $X,Y$ 的行中，只有 heavy $A,B$ 可能单独占一个 run。

端簇至少两点与 light 非 singleton 这两个输入本身来自原 single-delete debt；在它们的基础上，下文不再追加 heavy singleton 的跨行收费或多删预算。不需要选择最近邻，故距离 ties 与此证明无关。$A$ 的 HA acute cone 角界也未使用：这个局部 run 引理只需 $B$ 为 HM，另一个 heavy 为 $A$，而其余五点都是 light。所有论证始终在原七点配置中进行，不发生删除，不引入删除后子凸包的任何假设。

### 三角形传递规则

把 $B$ 的两个端簇也称为该行的两个 runs，以统一措辞。对 $P\in\{B,X,Y\}$ 和互异的实际点 $P,C,Z$，若

\[
\angle PCZ\ge3\lambda,
\]

则 $C,Z$ 在 $P$ 的同一 run。否则 $\angle CPZ\ge2\lambda$，这两个三角形角之和至少为 $5\lambda>\pi$。以下每次“传递”都只使用这一实际三角形规则。

## 2. Rigid 三角形恰有一个 small 角

考虑原实际三角形 $BXY$。其每个角要么 small，即至多 $R$，要么 large，即至少 $2\lambda$。这是 $B$ 的端簇以及 $X,Y$ 的 runs 的二分角界；因为 $R<2\lambda$，两种情形互斥。

* 三个角都 small 时，角和至多 $3R<\pi$，不可能。
* 恰两个角 small 时，第三角至少为 $\pi-2R>\pi-\lambda$，违反原实际角上界。
* 没有 small 角时，三个角均 large，角和至少为 $6\lambda>\pi$，不可能。

因此 $BXY$ **恰有一个 small 角和两个 large 角**。任一个角都不能达到 $3\lambda$：若某角至少为 $3\lambda$，它必为 large，另外还有一个 large 角，二者之和至少为 $5\lambda>\pi$。

在 $X$，$B,Y$ 因而不能一个在 apex、另一个在 nonapex；在 $Y$，$B,X$ 也不能一个在 apex、另一个在 nonapex。此时尚未断言两者在 nonapex 时属于不同 runs。

## 3. 两个其他 rigid 不能一起占 interior apex

假设 $B,Y$ 都在 $X$ 的 apex。则

\[
\angle BXY\le R.
\]

由第 2 节，$Y$ 处的角 $\angle BYX$ 是 large。结合该角不能达到 $3\lambda$，可知 $B,X$ 在 $Y$ 的两个不同 nonapex runs：它们不能跨 apex/nonapex，也不能同处 apex 或同处一个 nonapex run。

令 $K$ 为 $Y$ 的 apex 点集。它非空，且 $K\subset D$。对任意 $z\in K$，$X$ 在 $Y$ 的 nonapex，故

\[
\angle XYz\ge3\lambda.
\]

传递到 $X$ 得 $Y,z$ 同 run，即 $z$ 也在 $X$ 的 apex。因此

\[
K\subset D\cap\{\text{$X$ 的 apex 点}\}.
\]

现在检查 $X$ 的另外两个非空 runs。它们只能由 $D$ 中的点填充，因为 $B,Y$ 已在 apex。

* 若 $A$ 在这两个 nonapex runs 中，含 $A$ 的 run 至少需一点，另一个只含 light 的 run 至少需两点，所以两 runs 合计至少使用 $D$ 中三点。另一方面，$K$ 不含 $A$，是非空的全 light apex，故至少含两点；它们都在 $X$ 的 apex，与前述三点不交。这要求 $|D|\ge5$，矛盾。
* 若 $A$ 在 $X$ 的 apex，两个 nonapex runs 都只能使用三个 hull light。每个都不能为 light singleton，合计至少需四点，仍然矛盾。

故 $B,Y$ 不能一起占 $X$ 的 apex。交换 $X,Y$ 后同理。结合第 2 节，得到：

\[
\begin{aligned}
&B,Y\text{ 在 }X\text{ 都是 nonapex};\\
&B,X\text{ 在 }Y\text{ 都是 nonapex}.
\end{aligned}
\]

## 4. 两个非空 apex 不交，剩余至多一个 hull light

令 $U,V$ 分别为 $X,Y$ 的 apex 点集。由第 3 节，

\[
\varnothing\ne U\subset D,\qquad
\varnothing\ne V\subset D.
\]

若 $z\in U\cap V$，因为 $Y$ 在 $X$ 的 nonapex、$X$ 在 $Y$ 的 nonapex，三角形 $XYz$ 有

\[
\angle YXz\ge3\lambda,\qquad
\angle XYz\ge3\lambda.
\]

两角和至少为 $6\lambda>\pi$，矛盾。因此 $U\cap V=\varnothing$。

$U$ 或 $V$ 若为 singleton，其唯一成员必须是 $A$；三个 hull light 都不能单独占一个 interior run。若 $A\notin U\cup V$，两个非空 apex 都全为 light，故各至少含两点；不交性将要求至少四个 hull light，但 $|H|=3$。所以

\[
A\in U\cup V.
\]

两个不交的非空 apex 也不能同时为 singleton，因为唯一允许的 singleton 点都是 $A$。因此

\[
|U|+|V|\ge3.
\]

记

\[
W=D\setminus(U\cup V).
\]

则 $W\subset H$ 且 $|W|\le1$。这同时覆盖两 apex 各有至少两点，以及其中一个恰为 $\{A\}$ 的情形。

## 5. 两个 rigid 方向实际上分居 nonapex runs

对任意 $z\in V$，在 $Y$ 有 $\angle XYz\ge3\lambda$。传递到 $X$，得到 $Y,z$ 同 run。所以 $V$ 的全部射线都加入 $X$ 的含 $Y$ nonapex run。对称地，$U$ 的全部射线都加入 $Y$ 的含 $X$ nonapex run。

若 $B$ 也加入 $X$ 的含 $Y$ run，那么 $X$ 的 apex 是 $U$，该 nonapex run 已含 $\{B,Y\}\cup V$，第三个 run 只能由 $W$ 中的点组成。它必须非空，但 $W$ 至多含一个 light；这将产生 forbidden light singleton。故 $B,Y$ 在 $X$ 必属于两个不同的 nonapex runs。

同理，$B,X$ 在 $Y$ 必属于两个不同的 nonapex runs。因此

\[
\angle BXY\ge2\lambda,\qquad
\angle BYX\ge2\lambda.
\]

三角形角和给

\[
\angle XBY\le\pi-4\lambda=R<2\lambda.
\]

所以 $X,Y$ 在 $B$ 的同一端簇。这里的“不同 nonapex runs”是上述计数推出的结论，并非第 2 节预先附加的假设。

## 6. HM 的一个端簇被迫含至少五点

对任意 $z\in U$，$z$ 在 $X$ 的 apex，而 $B$ 在其 nonapex，故

\[
\angle BXz\ge3\lambda.
\]

传递到 $B$，得到 $X,z$ 在同一端簇。对任意 $z\in V$，同理从 $\angle BYz\ge3\lambda$ 得 $Y,z$ 在 $B$ 的同一端簇。

第 5 节已经证明 $X,Y$ 在 $B$ 同端。因此该端簇包含

\[
\{X,Y\}\cup U\cup V.
\]

这些点互异，且 $U\cap V=\varnothing$，所以其基数至少为

\[
2+|U|+|V|\ge5.
\]

$B$ 原来总共只有六条射线，另一端簇至多含一条射线。这违反原 HM 每个实际端簇至少含两条射线的 single-delete 结论。

故原 fullHull 为 HA+HM+LI3 五边形、另有两个 interior light 的 $t=2,N=7$ 实际配置不可能。

## 7. 合并冻结分支后的范围

本 note 排除的只是上述 HA+HM pentagon。由 [七点 HM2 rigid note 的第 4 节](JSP404_F18_T2_N7_RIGID_OCT7.md)，它是结合已有四顶点、HO、HM2 排除后唯一剩余的 $t=2,N=7$ 类型。因此，这四份纸面证明合起来闭合全部 $t=2,N=7$ 分支。

$t=0,1$ 的剩余八点、九点分支仍然开放；这里没有据此声称全部 F18 完成。上述结论是实际几何纸面结论，没有 Lean 编译或形式化完成声明，也没有使用未知 equality 分类。
