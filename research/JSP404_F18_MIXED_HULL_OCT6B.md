# F18 mixed fullHull：删除账本、最近邻及最小残余

日期：2026-10-07。任务标签保留 OCT6B。

状态：纸面数学；没有 Lean 修改或 Lean PASS 声明，没有构建、Git 操作或弱模型 SAT 当作实际配置。本文件仅研究合法有限实际平面点集。已排除的两个三角形子域不在这里重述。

## 1. 假设、记号与直接的 proper-subset 账本

固定 minimal actual F18 counter $P$，

\[
2\pi/9<\lambda\le\pi/4,\qquad R=\pi-4\lambda<\lambda/2.
\]

所有实际三点角均不超过 $\pi-\lambda$，故没有三点共线。每行 projective gaps 的和为 $\pi$，

\[
s(g)=\max(\lfloor g/\lambda\rfloor-1,0),\quad
\kappa_i=\sum_gs(g),\quad F=\sum_i2^{\kappa_i}=18.
\]

使用已建立的 actual reduction：所有行 $\kappa\in\{1,2\}$，所有 heavy（$\kappa=2$）都是**原点集的满凸包顶点**，heavy 数 $t\le3$。记 light 总数 $L$，总点数 $N$，hull light 数 $\ell$，interior light 数 $I$，则

\[
L+2t=9,\quad N=9-t,\quad h=t+\ell,\quad I=L-\ell.
\]

每个 light 单删总增益为零；每个 heavy 单删的总增益预算为 $2$。任一 heavy 行的 gain $1$ 已收费 $4$，故任何单点删除在所有保留 heavy 行均为零增益。

下文多删不把中间点集当作 critical。直接对原 counter 的 proper actual subset 应用归纳容量：若删集 $D$ 留至少三个点，累计增益收费满足

\[
\sum_{i\notin D}2^{\kappa_i}
 (2^{\kappa_i(P\setminus D)-\kappa_i(P)}-1)
 \le \sum_{q\in D}2^{\kappa_q}-2.
\]

特别是删 $k$ 个 light 的预算是 $2k-2$。删两个 light 的预算恰为 $2$，所以**所有保留 heavy 行的累计 score 增长均为零**；最多一个保留 light 行增长 $1$。

## 2. 使用的三 run 与度量引理

Interior light 行恰有三个 twisted sign flips。唯一 score $1$ gap 必为 flip，记其长度 $u\ge2\lambda$，另两 flips $v,w\ge\lambda$。三 runs 的总宽至多 $R$。

同 run 夹角至多 $R<\lambda/2$；异 run 夹角至少 $2\lambda$。位于两个小 flips 之间的 run 称 apex run，它与其余两 runs 的实际夹角至少 $3\lambda$。这些是实际有向射线簇，不把 projective arc 直接当实际夹角。

删除一条射线的行增益精确为：该射线是 run singleton 时为 $1$，否则为 $0$。因此 light 射线在任何 interior light 行不能为 singleton；每个 heavy 至多在一个 light 行发生收费 $2$ 的 singleton 事件。

度量事实：若在中心 $A$ 有另一点 $J\ne Q$，

\[
\theta=\angle QAJ<\lambda/2,
\]

则合法性给 $\angle AQJ\le\pi-\lambda$，故

\[
\angle AJQ\ge\lambda-\theta>\theta,
\quad QJ<AQ.
\]

所以 $A$ 不能是 $Q$ 的最近邻。这里假想最近邻条件是 $AQ\le QJ$，没有交换方向。

结论：interior light 不能成为任何 light 点的最近邻。它若成为 heavy $Q$ 的最近邻，则 $Q$ 在该 interior 行必为 singleton，删除 $Q$ 会暴露该 interior 点并收费 $2$。

另一个通用事实：若 $U,V$ 互为最近邻（允许距离相等），则对于任意第三点 $B$，

\[
UV\le BU,\quad UV\le BV
\quad\Longrightarrow\quad \angle UBV\le\pi/3.
\]

本文所有最近邻论证允许 ties；先任取一个最近邻函数，再使用严格的几何排除。

## 3. FullHull 类型与容量

对原 fullHull 顶点，令实际 hull 内角为 $\alpha$，外 projective gap 为 $e=\pi-\alpha\ge\lambda$。类型如下。

| 类型 | 行 | 外 gap | hull 内角 / 结构 |
|---|---:|---|---|
| HA | heavy | score 2，$e\ge3\lambda$ | $\alpha\le\pi-3\lambda<\pi/3$ |
| HM | heavy | score 1 | $2\lambda\le\alpha\le\pi-2\lambda$，唯一内 big gap $\ge2\lambda$ |
| HO | heavy | score 0 | $\alpha\ge3\lambda$，唯一内 big gap $\ge3\lambda$ |
| LB | light | score 1，$2\lambda\le e<3\lambda$ | big gap 是外 gap |
| LI | light | score 0，$\lambda\le e<2\lambda$ | 唯一内 big gap $\ge2\lambda$ |

HM、HO 的两端簇总宽至多 $R$。若其某端簇仅有一点 $Q$，删除 $Q$ 合并外 gap 与内 big gap：HM 的两者至少为 $2\lambda+2\lambda$，HO 至少为 $\lambda+3\lambda$。合并后 score 至少 $3$，原贡献为 $2$，即 heavy 行 gain 至少 $1$、收费至少 $4>2$。因此在原 F18 配置，**HM/HO 每端簇都非 singleton**。

于是每个 $Q\ne B$ 都有同端簇 witness $J$，夹角至多 $R<\lambda/2$，严格给 $QJ<BQ$。所以 **HM/HO 不能成为任何实际点的最近邻**，不只 light 点。

HA 的最近邻承接容量至多 $1$：其 cone 宽度严格小于 $\pi/3$。Hull light 容量至多 $2$：LB cone 小于 $2\pi/3$；LI 内 big gap 将 cone 分成两个各宽小于 $\pi/3$ 的端簇。

对 interior targets 可加强：LB 容量至多 $1$。Interior target 若以 hull 顶点为最近邻，它到两条 hull 边界射线的角距均至少 $\lambda/2$，否则边界 hull 邻点更近。LB cone 宽度至多 $\pi-2\lambda<\lambda+\pi/3$，放不下两个角距至少 $\pi/3$ 且各有上述边界余量的 targets。LI 若承接两个 interior targets，则两个端簇各宽至少 $\lambda/2$，故其内角必至少 $3\lambda$。

记 HA 数为 $a$，HM 数为 $d$，LB 数为 $b$。总 light 最近邻及全点最近邻分别给

\[
L\le2\ell+a,
\qquad
N\le2\ell+a+u,
\]

其中 $u\le t$ 是选择 interior 最近邻的 heavy 数。因此至少

\[
D=\max(0,N-2\ell-a)
\]

个不同 heavy 删除会各暴露一个 interior light（这些暴露点不一定互异）。

凸包转角总和给离散限制

\[
K:=h+2a+d+b\le8.
\]

理由是每种类型的外 gap 基预算分别为 $3,2,1,2,1$ 倍 $\lambda$，而 $2\pi/\lambda<9$。特别是 $h\le8$、$a\le2$。

## 4. 删除 fullHull light 的实际几何结论

删除一个 light $Q$ 时，在每个原 interior light 行，$Q$ 不是 run singleton；删除后原三个 runs 仍均非空，仍有三个 flips，因此该点仍 interior。其他原 fullHull 顶点在子集中仍为极点。因此

\[
\operatorname{fullHull}(P\setminus\{Q\})
=\operatorname{fullHull}(P)\setminus\{Q\}.
\]

这是从实际三 run 证明的结论，不是默认把原凸包与子集凸包混同。删除一个 heavy 最多暴露一个 interior light，因为每个暴露行需要 singleton gain $1$、收费 $2$。

若 $Q$ 是 light hull 顶点，其删除还保持所有剩余 hull 顶点的外 gap score。对其 hull 邻点，若被合并的内 gap score 正，则外 gap 至少 $\lambda$ 会产生正删除增益；因此该内 gap score 必为零，而零总增益迫外 score 不变。于是 HA/HM/HO/LB/LI 类型在**一次 light hull 删除**下不变。

这也表明该 light ear 没有其他实际点。不能把此单删结论自动迭代到第二删；第二删使用第 1 节的直接 ledger。

## 5. 四顶点 fullHull 的精确分类

由总 light 容量、外类型在单删 light 下不变、以及 $K\le8$，$h=4$ 的可能类型只能是：

| $t$ | $N$ | 四个 hull 顶点 | $I$ |
|---:|---:|---|---:|
| 1 | 8 | HA + LB + LB + LI | 4 |
| 2 | 7 | HA + HA + LI + LI | 3 |
| 3 | 6 | HA + HA + HO + LI | 2 |

说明：删一个 light hull 得到三角形，并保留其余类型。

* 一 heavy、两 light 的三角形，heavy 只能 HA；两个 light 不可能同时 LI。对原四边形任意 light 单删，推出至少两个 LB；$K\le8$ 又迫恰两个 LB。
* 两 heavy、一 light 的三角形不能含 HO，不能有两个 HM。若为 HA+HM，则保留 light 必为 LB；原两 light 均 LB 会使 $K\ge9$。故原两 heavy 均 HA，再由 $K\le8$ 两 light 均 LI。
* 三 heavy 的三角形必须两 HA 加一个非 acute。原 $h=4$ 已有两 HA，$K\le8$ 排除 HM 与 LB，故第三 heavy 是 HO、唯一 light 是 LI。

## 6. 排除 $N=6,h=3,4$

先补齐 $h=3$ 的完整分支：满凸包恰为三个 heavy，三个 light 均 interior。三个 heavy hull 角若全 HA，则角和至多 $3(\pi-3\lambda)<\pi$；若两个非 HA 中包含 HO，两角和至少 $5\lambda>\pi$；若两个均 HM，第三角至多 $R$，该第三顶点的整行外 gap 至少 $4\lambda$，强迫 $\kappa\ge3$。所以恰有两 HA、一个 nonacute heavy。第 2 节迫三 interior light 的最近邻均在原满凸包；第 3 节给两 HA 总容量 $2$、nonacute heavy 容量 $0$，不足承接三个 light。这只补齐 $t=3$ 的三角形分支，不重述无 heavy 的另一个三角形子域。

以下处理 $h=4$。

记 HA 为 $A,C$，HO 为 $B$，hull LI 为 $Q$，interior light 为 $X,Y$。

HO $B$ 的两端簇大小为 $2,3$，簇宽至多 $R$，跨簇角至少 $3\lambda>\pi/2$。跨簇 $U,V$ 满足 $UV>BU,BV$。又第 3 节给每个 $U\ne B$ 同簇 witness 距离严格小于 $BU$，故每个 $U\ne B$ 的最近邻严格留在同簇。这里显式联合了 witness，不能单凭跨簇不等式排除 $B$。

每簇必须有一个 HA：$Q$ 需要同簇 HA 作最近邻，另一簇若只含 interior light 就没有可用最近邻。两 HA 各一个。分法 $\{A,Q\}\mid\{C,X,Y}$ 不可能，因为 $X,Y$ 都只能最近于同一个 HA，而 HA 容量为 $1$。故重命名后

\[
\{A,X\}\mid\{C,Q,Y\}.
\]

于是 $A\leftrightarrow X$，$Q\to C$。由 $CQ\le QY$，三角形 $CQY$ 在 $Y$ 的角不大于在 $C$ 的角；后者小于 $\pi/3<2\lambda$。所以 $C,Q$ 在 $Y$ 的同一 run。

又 $\angle XBY\ge3\lambda$。若 $B,X$ 在 $Y$ 的异 run，则 $\angle BYX\ge2\lambda$，两个角之和至少 $5\lambda>\pi$，矛盾。因此 $B,X$ 在 $Y$ 的同一 run。

$Y$ 总共五条射线。两对 $(C,Q)$、$(B,X)$ 必是两个不同 runs：若合在一 run，剩余仅 $A$，放不满三个非空 runs。故 $A$ 在 $Y$ 行 singleton。

而 $A\to X$ 且 $X$ interior，迫 $A$ 在 $X$ 行也 singleton；否则同 run witness 严格更近于 $A$。删除 $A$ 的两行收费 $2+2=4>2$，矛盾。全证允许最近邻 ties。

## 7. 排除 $N=6,h=5$

此时有两个 hull light $Q,R$，唯一 interior light $X$。由 $K\le8$，$a\le1$。

### 7.1 $a=1$

记 HA 为 $A$，另两个 heavy 为 $B,C$。有 $d+b\le1$，所以至少一个 heavy 是 HO，设为 $B$。

HO 的最近邻隔离与 $2/3$ 簇大小，联合 HA 容量 $1$、nonacute heavy 容量 $0$、interior light 不承接 light，穷尽二点簇的十种选法，只有

\[
\{A,X\}\mid\{Q,R,C\},
\qquad
\{Q,R\}\mid\{A,C,X\}
\]

可能。两种都迫 $A\leftrightarrow X$、$Q\leftrightarrow R$。直接删 light $Q,R$ 的预算是 $2$，禁止清空任何 heavy 端簇：清空会把外 gap 与内 big gap 合并为至少 $4\lambda$，收费至少 $4$。故第二种不可能，$B$ 的分簇必须是第一种。

若 $C$ 也是 HO，同理其分簇为 $\{A,X\}\mid\{Q,R,B}$，三角形 $BCX$ 在 $B,C$ 各至少 $3\lambda$，矛盾。

若 $C$ 是 HM，互为最近邻的 $Q,R$ 在其同一端簇。三角形 $BCX$ 在 $B$ 已至少 $3\lambda$，故 $B,X$ 也必须在 $C$ 同簇，否则在 $C$ 再至少 $2\lambda$。这两对不能合在同一端簇：否则该簇有四点而另一簇仅 $A$，违反 heavy 两端簇均非 singleton。二删预算再排除 $\{Q,R\}$ 单独一簇，迫

\[
C:\quad \{B,X\}\mid\{A,Q,R\}.
\]

但 $A\leftrightarrow X$ 的一对在 $C$ 跨至少 $2\lambda>\pi/3$，与 mutual pair 的通用角界矛盾。

### 7.2 $a=0$ 且含 HO

所有 heavy 都不能成为任何点的最近邻。故 $Q\leftrightarrow R$，$X$ 最近于 $Q$ 或 $R$。若存在 HO，其最近邻隔离迫 $Q,R,X$ 同簇；另一簇只有另两个 nonacute heavy，彼此及中心均不能承接最近邻，矛盾。

### 7.3 剩余 HM + HM + HM + LI + LI

同样有 $Q\leftrightarrow R$，$X$ 最近于 $Q$ 或 $R$。所以三角形 $QRX$ 在 $X$ 的角至多 $\pi/3<2\lambda$，即 $Q,R$ 在 $X$ 的同一 run。

在每个 heavy 行，互为最近邻的 $Q,R$ 同端簇。二删预算禁止清空该簇，所以该原簇恰为 $\{Q,R,Z\}$，另一簇有两点。删 $Q,R$ 后所有三 heavy 仍为 HM：外 gap 与内 big gap 各至少 $2\lambda$，两端簇均保留，而总 $\kappa=2$。

若 $X$ 仍 interior，满凸包是三个 HM 的三角形，其角之和至少 $6\lambda>\pi$，不可能。故 $X$ 暴露，增长 $1$ 收费 $2$，新 $\kappa_X=2$。被整删的 run 恰为 $\{Q,R\}$。唯一剩余 flip 原 score 是 $0$ 或 $1$，故新 $X$ 为 HO 或 HM，不能 HA；HO 与三个 HM 的四边形角和至少 $9\lambda>2\pi$，所以新 $X$ 也是 HM。

需要一个实际四点引理：**四个 HM 顶点的四边形，其 singleton-neighbor mapping 是两个 mutual pairs。** 每顶点在另一三点中有一个孤立的邻边顶点，另两个方向夹角至多 $R$；孤立邻边与对角射线夹角至少 $2\lambda$。沿四边形记孤立邻边的选择为 $+/-$。若相对顶点选择不同，则某三角形三个角各至少 $2\lambda$，不可能；故相对选择相同。若四点同向选择，则每个连续三角形给下一边严格长于上一边（big angle $\ge2\lambda>R\ge$ small angle），形成边长严格循环，亦不可能。余下恰是两个 mutual pairs。这里指互为 singleton neighbor，未断言这两对是最近邻。

在两对中，一对不含新 $X$，记为原 heavy $U,V$。删 $Q,R$ 后 $V$ 是 $U$ 的 singleton；原 $U$ 行的含 $Q,R$ 三点端簇因此正是 $\{Q,R,V\}$。同理原 $V$ 行该端簇为 $\{Q,R,U\}$。所以

\[
\angle QUV\le R,\quad \angle QVU\le R,
\]

第三角至少 $\pi-2R>\pi-\lambda$，违反合法性。

## 8. 排除 $N=6,h=6$

此时全部点都在满凸包，有三个 hull light。

若 $a=0$，$K\le8$ 迫存在 HO。其二点簇不能含 nonacute heavy，否则另一个点没有可用最近邻，所以该簇含两个 light；三点簇余下一 light 加两 nonacute heavy，该 light 又没有可用最近邻，矛盾。

若 $a=1$，$K\le8$ 迫类型为 HA $A$、HO $B,C$、三个 LI。任选一个最近邻函数。HO 的二点簇不能含另一个 HO，否则其中 active 点没有可用最近邻；故二点簇是两个互为最近邻的 active 点。三点簇含另两个 active 点与 nonacute heavy：若两 active 都为 light，它们互为最近邻；若为 HA 与一个 light，该 light 只能选 HA、HA 只能选该 light，HA 容量 $1$ 再排除 nonacute heavy 选 HA。于是 active 四点组成两 mutual pairs：$A\leftrightarrow S$，其余 $Q\leftrightarrow R$。两对在每个 HO 行各位于同一端簇。

直接删 light $Q,R$ 禁止清空 HO 端簇，所以原 $B$ 行必须有端簇 $\{Q,R,C\}$，原 $C$ 行必须有端簇 $\{Q,R,B\}$。于是

\[
\angle QBC\le R,\quad\angle QCB\le R,
\]

再次违反第三角上界。

因此由第 6–8 节，**F18 的整个 $t=3,N=6$ 分支已在纸面闭合**。这不是 Lean 完成声明。

## 9. $t=0,1,2$ 的精确剩余账本

下表只列尚未由本文排除的范围；每行还须满足类型计数及 $K=h+2a+d+b\le8$。

| $t$ | $N,L$ | hull light 数 $\ell$ | 必要限制 |
|---:|---|---|---|
| 0 | $9,9$ | $5,6,7,8$ | 全部 hull 为 light，$b\le8-\ell$ |
| 1 | $8,7$ | $3,4,5,6,7$ | $\ell=3$ 恰 HA+LB2+LI；$\ell\ge4$ 仍未闭合 |
| 2 | $7,5$ | $2,3,4,5$ | $\ell=2$ 恰 HA2+LI2；其余见下表 |

最小未闭合实际点数是 $N=7,t=2$：

| $h,\ell,I$ | 仍允许的精确类型条件 |
|---|---|
| $4,2,3$ | HA2 + LI2 |
| $5,3,2$ | $a\in\{0,1\}$，$d+b\le3-2a$；$a=0$ 时至少一个 heavy 最近于 interior |
| $6,4,1$ | $a\in\{0,1\}$，$d+b\le2-2a$；$a=1$ 时恰 HA+HO+LI4 |
| $7,5,0$ | $a=0,d+b\le1$：HO2 且 $b\le1$，或 HM+HO 且 $b=0$ |

这是真实配置的必要条件表，不声称表中每一模式可实际实现，也不把整数可行性当 actual counter。

## 10. 最小残余的进一步严格结构与下一步命题

重点残余是 $N=7,h=4$：两 HA $A,C$、两 hull LI $Q,R$、三 interior light $X,Y,Z$。

直接删 $Q,R$ 后基质量为 $14$、预算为 $2$。两 heavy 保持 $\kappa=2$。满凸包不能只有 $A,C$，所以至少一个原 interior 暴露；每个暴露行至少增长 $1$、收费 $2$，故恰一个暴露，设为 $X$，新 $\kappa_X=2$，另外 $Y,Z$ 保持 interior 与 $\kappa=1$。新满凸包是 $A,C,X$ 的三角形，potential 恰为 $16$。

原 $X$ 行被整删的 run 必恰为 $\{Q,R\}$。其余四射线 $A,C,Y,Z$ 分为两个 runs，有两种可能：二点加二点，或一个 HA singleton 加另外三个点。因此原 $X$ 行 run 大小为 $(2,2,2)$ 或 $(1,2,3)$；后一种的 singleton 必是 $A$ 或 $C$。不能把 light 不为 singleton 误推成所有 runs 都为二点。

全点最近邻计数 $7>2\ell+a=6$ 迫至少一个 heavy $A$ 或 $C$ 最近于某个 interior light $T$；相应 heavy 在 $T$ 行 singleton，单删预算全部耗尽，并暴露 $T$。若 $X$ 的形状为 $(2,2,2)$，则 $T\ne X$；若为 $(1,2,3)$，可以 $T=X$，不能默认两种删除暴露不同点。

下一步应证明或给实际负控的几何命题是：

> 不存在合法实际七点配置，具有上述 HA2+LI2 原四边形及三 interior light，满足（i）所有 light 单删 gain 为零；（ii）所有 heavy 单删预算至多 $2$；（iii）直接删 $Q,R$ 恰暴露 $X$，原 $X$ 有完整 run $\{Q,R\}$，且形状为 $(2,2,2)$ 或 $(1,2,3)$；（iv）某 interior light $T$ 含 HA singleton 并作为该 HA 的最近邻，允许后一种形状下 $T=X$。

这是真实射线、满凸包和距离的命题。它没有预设五点 $F=16$ equality 的未知分类。可以先按 $(2,2,2)/(1,2,3)$ 分流；前者再区分两个剩余 runs 为 $(A,Y),(C,Z)$ 还是 $(A,C),(Y,Z)$，后者追踪单点 HA 与 HA-singleton 最近邻事件是否重合。

本文未排除 $t=0,1,2$ 的全部模式；未把一次 light 删除后的点集重新当作原 critical counter，未从 GlobalFiveLow 的容量结论杜撰 equality 结构。
