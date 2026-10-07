# F18：两 heavy、七点、四顶点 fullHull 的纸面排除

日期：2026-10-07。状态：actual 几何纸面证明；没有 Lean PASS、构建或 Git 操作。

本 note 接续已冻结的 [mixed-hull paper](JSP404_F18_MIXED_HULL_OCT6B.md)，其 SHA256 为 bd02ed011e6c4013250e6165526861c49af1c4aa22b0dc0d8caf4be7feb1eaa9。冻结稿第 10 节所列四顶点七点残余在本 note 中排除；不修改冻结稿，也不声称全部 F18 已闭合。

## 1. 配置与可用事实

固定 minimal actual F18 counter，$2\pi/9<\lambda\le\pi/4$，$R=\pi-4\lambda<\lambda/2$。本分支有两 heavy $A,C$、两个 hull light $Q,R$、三个 interior light。原满凸包是 HA2+LI2 四边形：

* $A,C$ 的 fullHull 内角均小于 $\pi/3$；
* $Q,R$ 各有一个内 big gap，最近邻承接容量至多 $2$；
* 每个 interior light 恰有三个实际方向 runs，总宽至多 $R$。同 run 角至多 $R$，异 run 角至少 $2\lambda$；apex run 与另外两 runs 的角至少 $3\lambda$；
* 原 light 删除总增益为零；每个 heavy 删除总预算为 $2$。一个 interior 行的 heavy singleton 收费 $2$，所以每个 heavy 至多在一个 interior light 行为 singleton；
* interior light 不能成为 light 点的最近邻；若成为 heavy 的最近邻，该 heavy 必为其 run singleton；
* 任意 mutual nearest pair 在任何第三点处的夹角至多 $\pi/3$，所以在 interior 行必处于同一 run；
* 直接删两个原 light 的 proper-subset 预算是 $2$，不是把第一次删除后的点集重新当 critical。

最近邻可任意选择一个函数，允许距离 ties。以下排除均使用严格角界或严格距离界。

## 2. 删两个 hull light 恰暴露一个 interior

删 $Q,R$ 的原基质量是 $14$，累计增益预算 $2$。两原 heavy 行不能增长，因为一次增长已收费 $4$。

其他剩余原凸包顶点只有 $A,C$，而合法五点子集不能共线，因此至少一个原 interior 成为新 hull 顶点。原 interior 的三个 runs 只有在删空一个 run 时才失去 interior 身份。原 light 不可能 singleton，所以删空的 run 必恰为 $\{Q,R\}$。合并两相邻 flips 及该 run 的内部 gap，长度为对应基阈值加至多 $R<\lambda$，行增益恰为 $1$、收费 $2$。

故恰一个 interior 被暴露；它的原 run 正好是 $\{Q,R\}$。另外两个 interior 的该 run 不能被删空。此结论同时控制几何暴露与收费，没有默认原 hull 等于子集 hull。

## 3. Acute hull 点的最近邻入度

设 HA 点 $A$ 的选择最近邻为 $T$，令 $d=AT\le AJ=r$。对任意 $J\ne A,T$，两射线在 acute cone 内夹角 $\theta<\pi/3$，故

\[
TJ^2=d^2+r^2-2dr\cos\theta
 <r^2+d(d-r)\le r^2.
\]

因此 $TJ<AJ$，$A$ 不能成为 $J$ 的最近邻。HA 点的最近邻入度只能是 $0$ 或 $1$，入度 $1$ 时它与自己的选择最近邻互为最近邻。

两 HA 点不能互相作为最近邻。取任意第三点，两 HA 处的三角形角均小于 $\pi/3$，第三角大于 $\pi/3$，所以 HA–HA 边严格长于另外两边。

记：

* $u$：选择 interior 最近邻的 heavy 数；
* $r$：有最近邻入边的 HA 数，即 HA 参与 mutual nearest pair 的数；
* $v$：两个 hull light 的最近邻总入度。

Interior 最近邻只能承接 heavy，所以所有七条最近邻边给

\[
7=u+r+v,\qquad u\le2,\quad r\le2,\quad v\le4.
\]

因此 $u+r\ge3$，仅有三种情形：

\[
(u,r)=(1,2),\quad (2,2),\quad (2,1).
\]

## 4. 排除 $(u,r)=(1,2)$

重命名后，最近邻关系必为

\[
A\leftrightarrow P,\qquad C\leftrightarrow Q,
\qquad R\to Q,\qquad S,T\to R,
\]

其中 $P,S,T$ 为三个 interior light。理由：一 HA 与 interior mutual，另一 HA 与 hull light mutual；两 HA 入度均已占满。另一 hull light 只能选 $Q$；$Q$ 入度被 $C,R$ 占满，所以另外两个 interior 必选 $R$。

在 $S$ 行，两 disjoint mutual pairs $\{A,P\}$、$\{C,Q\}$ 各在同一 run。它们不能合并为同一 run，否则剩余 light $R,T$ 会迫出 light singleton。三个非空 runs 因此精确为

\[
S:\quad \{A,P\},\ \{C,Q\},\ \{R,T\}.
\]

同理

\[
T:\quad \{A,P\},\ \{C,Q\},\ \{R,S\}.
\]

删 $Q,R$ 不会删空 $S,T$ 的任何 run，故第 2 节的唯一暴露点必须是 $P$，其 run 必须恰为 $\{Q,R\}$。

但 mutual pair $\{C,Q\}$ 在 $P$ 行同 run，$Q$ 的 run 含 $C$，不可能恰为 $\{Q,R\}$，矛盾。

## 5. 排除 $(u,r)=(2,2)$

此时两 HA 分别与不同 interior mutual，记

\[
A\leftrightarrow P,\qquad C\leftrightarrow S.
\]

两 HA 入度已满，故 $Q\leftrightarrow R$，第三 interior $T$ 最近于 $Q$ 或 $R$。

在 $T$ 行，三个 disjoint mutual pairs 覆盖六条射线，恰为三个 runs：

\[
T:\quad \{A,P\},\ \{C,S\},\ \{Q,R\}.
\]

因此删 $Q,R$ 会暴露 $T$、耗尽预算。$P,S$ 不能再暴露。

$A$ 在 $P$ 行为 singleton；disjoint mutual pairs $\{C,S\}$、$\{Q,R\}$ 各同 run，剩余 light $T$ 必加入其中之一。为防止 $\{Q,R\}$ 被删空，$T$ 必加入它。于是

\[
P:\quad \{A\},\ \{C,S\},\ \{Q,R,T\}.
\]

同理

\[
S:\quad \{C\},\ \{A,P\},\ \{Q,R,T\}.
\]

在三角形 $PST$ 的每个顶点，其余两点都属于不同 runs，所以三个角各至少 $2\lambda$；总和至少 $6\lambda>\pi$，矛盾。

## 6. 排除 $(u,r)=(2,1)$

唯一 HA mutual pair 记为 $A\leftrightarrow P$。另一 HA $C$ 的最近邻为某 interior，但不 mutual。只有 $A$ 承接一个 light，其余四个 light 的最近邻只能为 $Q,R$，所以

\[
Q\leftrightarrow R.
\]

### 6.1 $C\to P$ 不可能

此时 $A,C$ 在 $P$ 行都 singleton，耗尽各自的单删预算。因此 $C$ 在另外两个 interior $S,T$ 的行均不 singleton。

在 $S$ 行，mutual pairs $\{A,P\}$、$\{Q,R\}$ 各同 run，并且不能合在同一 run，否则第三 run 将产生 light singleton。剩余 $C,T$ 必构成第三 run，因为 $C$ 非 singleton。因此

\[
S:\quad \{A,P\},\ \{Q,R\},\ \{C,T\}.
\]

同理

\[
T:\quad \{A,P\},\ \{Q,R\},\ \{C,S\}.
\]

删 $Q,R$ 同时暴露 $S,T$、收费 $4>2$，矛盾。

### 6.2 $C\to S$ 的唯一 run 模式

令第三 interior 为 $T$。$C$ 在 $S$ 行 singleton，故在 $P,T$ 行都不能 singleton。

在 $T$ 行，mutual pairs $\{A,P\}$、$\{Q,R\}$ 各同 run、不能合并；剩余 $C,S$ 必构成第三 run：

\[
T:\quad \{A,P\},\ \{Q,R\},\ \{C,S\}.
\]

所以二删 $Q,R$ 已暴露 $T$，预算全部耗尽。$S$ 的 run 不能被删空：$C$ singleton，另外两 runs 分别含 $\{A,P\}$ 与 $\{Q,R\}$，剩余 light $T$ 必加入后者：

\[
S:\quad \{C\},\ \{A,P\},\ \{Q,R,T\}.
\]

在三角形 $PST$，$S,T$ 处两角已各至少 $2\lambda$。若 $P$ 处 $S,T$ 异 run，三个角至少 $6\lambda>\pi$。故 $S,T$ 在 $P$ 同 run。

在 $P$ 行，$A$ singleton，$\{Q,R\}$ 同 run，$C$ 不能 singleton。若 $S,T$ 与 $Q,R$ 同 run，剩余 $C$ 就 singleton，不可能。因此唯一模式是

\[
P:\quad \{A\},\ \{S,T\},\ \{Q,R,C\}.
\]

### 6.3 两个三角形迫出的 apex 矛盾

考虑三角形 $CPS$：

* 在 $P$，$C\in\{Q,R,C\}$、$S\in\{S,T\}$，异 run，角至少 $2\lambda$；
* 在 $S$，$C\in\{C\}$、$P\in\{A,P\}$，异 run，角至少 $2\lambda$。

若 $S$ 处上述两 runs 有一个是 apex，角至少 $3\lambda$，与 $P$ 的角之和至少 $5\lambda>\pi$。所以 $S$ 处的这两 runs 必为两个非 apex runs，迫其 apex 为

\[
\{Q,R,T\}.
\]

再看三角形 $PST$：在 $S$，$P$ 位于非 apex run $\{A,P\}$、$T$ 位于 apex run，故

\[
\angle PST\ge3\lambda.
\]

在 $T$，$P\in\{A,P\}$、$S\in\{C,S\}$，异 run，故

\[
\angle PTS\ge2\lambda.
\]

两角之和至少 $5\lambda>\pi$，矛盾。无需额外推断 $T$ 的 apex。

## 7. 结论与仍未闭合范围

三种最近邻计数情形全部排除，因此 **F18 的 $t=2,N=7,h=4$ 分支纸面闭合**。与冻结稿的 $t=3,N=6$ 全分支合并后，最小未闭合实际点数仍为七点，但其 hull 必至少五个顶点：

| $h,\ell,I$ | 尚未由这两份 paper 排除的类型限制 |
|---|---|
| $5,3,2$ | $a\in\{0,1\}$，$d+b\le3-2a$；$a=0$ 时至少一个 heavy 最近于 interior |
| $6,4,1$ | $a\in\{0,1\}$，$d+b\le2-2a$；$a=1$ 时恰 HA+HO+LI4 |
| $7,5,0$ | $a=0,d+b\le1$：HO2 且 $b\le1$，或 HM+HO 且 $b=0$ |

此外仍有冻结稿列出的 $t=0,1$ 分支。本 note 没有把纸面子域闭合当作原题全解，没有二次套用中间配置的原 critical debt，没有使用未知的五点 equality 分类。
