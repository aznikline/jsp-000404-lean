# F18：八点单 heavy 的 rigid 缩放、已排除分支与实际残余

日期：2026-10-07。状态：PAPER；没有 Lean/Git 操作、没有形式化 PASS 声明。三 run/apex 输入来自纸面实际几何；对应 actual AngleGap source 的检查状态由其负责人单独管理。本文件只记录数学推导，不把源码静态就绪当已检验证明。

固定 minimal actual F18 counter，$2\pi/9<\lambda\le\pi/4$，$R=\pi-4\lambda<\lambda/2$。八点分支恰有一个 heavy $A$，七个 light。记 hull 顶点数 $h$、hull light 数 $\ell=h-1$、interior light 数 $I=8-h$。

所有保留原 hull 顶点在任意子集中仍极点。删除子集后是否暴露原 interior 必须另证，不能默认 fullHull 等于原 hull 的删点结果。

## 1. 使用的原配置结构与直接账本

每个 interior light 有三个实际方向 runs，同 run 角至多 $R$，异 run 角至少 $2\lambda$；apex 与任一 nonapex 角至少 $3\lambda$。所有 light 射线不能在 interior 行 singleton。

Heavy 分 HA/HM/HO，外 gap score 分别为 $2/1/0$。HA hull cone 小于 $\pi/3$。HM/HO 各有两个总宽至多 $R$ 的实际端簇；跨簇分别至少 $2\lambda/3\lambda$。每端至少两点，否则原 heavy 行单删 gain 至少 $1$、收费 $4$，超过单点删除的总预算 $2$。

每个原 light 单删预算零，heavy 单删预算 $2$。直接删 $k$ 个原 light（保留至少三个点）的累计增益收费至多 $2k-2$。下文只对原 proper subset 使用此账本，不把中间配置重新当 critical。

## 2. Rigid 子集在 $2\lambda$ 处合法，至多四点

Rigid 指 HM/HO heavy 或 interior light。其任一观察角要么 $\le R$，要么 $\ge2\lambda$。

任意三个 rigid 的三角形恰有一个 small 角、两个 large 角：两个 small 角会使第三角超过 $\pi-\lambda$，三个 large 角之和至少 $6\lambda>\pi$。没有角能达到 $3\lambda$，因为它与另一个 large 角之和至少 $5\lambda>\pi$。

因此每个 rigid 三角形的每个角均至多 $\pi-2\lambda$。在参数

\[
\mu=2\lambda\in(4\pi/9,\pi/2]
\]

处，实际 rigid 子配置合法。至少三点时使用已经证明的 **n2 LOW actual capacity $4$**，其点数至多四；不足三点时该基数上界显然。这里调用的是实际容量定理，不是弱模型 SAT，也不是原 counter 的基数最小性。

若恰有四个 rigid，$\mu$ 处四个权重均至少为 $1$、总和至多 $4$，所以每行 $\mu$-score 都为零。它们全部在自己子配置凸包上：若某点 interior，另外三条射线围住它，必有一个实际角至少 $2\pi/3$，但 $\pi-\mu<2\pi/3$。

该 rigid 四边形的每个内角还必须 $\ge2\lambda$。若它是 small 角 $\alpha\le R$，其整行外 projective gap 至少

\[
\pi-\alpha\ge\pi-R=4\lambda=2\mu,
\]

给正 $\mu$-score，矛盾。

于是每个原 interior rigid 观察另外三个 rigid 时，它们分居两个 nonapex runs：不能有 apex/nonapex 横跨（会出现 rigid 三角形角 $\ge3\lambda$），不能全部在 apex（其两 rigid hull 邻点夹角至少 $2\lambda>R$）。

不同原 interior 的 active-only apex 集合互不相交：共享一点会在同一个实际三角形中产生两个至少 $3\lambda$ 的角。

## 3. R4 与 R3 排除八点的小 hull 情形

### 3.1 R4

若唯一 heavy 是 HM/HO，$I\ge4$ 给至少五 rigid，直接违反第 2 节。

若为 HM 且 $I=3,h=5$，四 rigid 是 heavy 加三个 interior。三个 interior 的 apices 均只含四个 hull light、每个至少两点、两两不交，需要至少六点，矛盾。

若为 HA 且 $I\ge5$，interior rigid 数至少五，亦不可能。若 HA 且 $I=4,h=4$，四个 interior 的 active apex 集取自唯一 HA 加三个 hull light，总共四点；至多一个 apex 可以是 HA singleton，其余各至少两点，总需求至少七点，矛盾。

### 3.2 HA、三个 interior：R3

设唯一 HA 为 $A$，interior 为 $X,Y,Z$，hull light 四点。Rigid 三角形 $XYZ$ 唯一 small 角设在 $X$。在 $Y,Z$ 处其他两个 rigid 分居 nonapex，故其 apices $U,V$ 只含 active 集 $\{A\}\cup HL_4$，并且 $U\cap V=\varnothing$。

$Y,Z$ 在 $X$ 同 run。对 $H\in U$，$Y$ 处角 $\angle XYH\ge3\lambda$，迫 $X$ 处 $Y,H$ 同 run；$V$ 同理。因此一个 $X$ run 包含 $\{Y,Z\}\cup U\cup V$。

若 $A\in U\cup V$，并集至少三点，该 run 至少五条，剩余至多两条且全是 light，填不满另外两个非 singleton runs。若 $A\notin U\cup V$，并集至少四点，该 run 至少六条、仅剩至多一条，仍填不满。故 HA 的 $I=3,h=5$ 分支排除。

### 3.3 HM、两个 interior：R3

Rigid 三角形为 $B,X,Y$。若唯一 small 角在 $X$，在 $Y$ 的 apex 至少含两个 hull light；传递到 $X$，它们与 $B,Y$ 同 run，至少四条。剩余至多三条且全为 light，填不满另外两个 runs。同理排除 small 在 $Y$。

若 small 在 HM $B$，$X,Y$ 同 B 端簇。在 $X,Y$，其他 rigid 分居 nonapex，因此两 apices 各至少两点、互不相交。角度传递迫全部 apex 点在 $B$ 与 $X,Y$ 同端，共至少六条；$B$ 共七条射线，另一端至多一条，违反端簇至少两点。故 HM 的 $I=2,h=6$ 排除。

## 4. 单 HO 不能与任何 interior 共存

设 heavy $B$ 为 HO，$X$ 为任意 interior。B 的反 X 端簇记为 $T$，$|T|\ge2$。

对 $V\in T$，$\angle XBV\ge3\lambda$，所以 $X$ 看到 $B,V$ 不能异 run，否则又有角至少 $2\lambda$。因此 $\{B\}\cup T$ 同 X run。

$X$ 共七条射线，另两个 runs 全部由 light 填充，各至少两点。故 $|T|+1\le3$，结合 $|T|\ge2$，得到 $T$ 恰两个 light。直接删它们清空保留 heavy 的端簇，收费至少 $4>2$，矛盾。

## 5. 转角预算后的三个实际残余模式

每个 hull light 至少消耗外 gap $\lambda$；HA/HM/HO 分别消耗 $3\lambda,2\lambda,\lambda$。若 LB 数为 $b$，转角离散预算是

\[
K=h+2a+d+b\le8,
\]

其中 $a,d$ 分别为 HA、HM 数。

因此 HA 的 $h\ge7$ 与 HM 的 $h=8$ 都已排除。结合第 3–4 节，八点仅剩：

| 原 fullHull | interior light | 额外结论 |
|---|---:|---|
| HA + LI5，$h=6$ | 2 | $K=8$，无 LB |
| HM + LI6，$h=7$ | 1 | $K=8$，无 LB |
| HO + LI7，$h=8$ | 0 | $K=8$，无 LB |

特别地，HA+$I=1,h=7$ 已由 $K\ge9$ 排除，不是尚待研究的模式。

## 6. Pure-LI 隔离块至少四点

这是三个剩余模式共用的实际几何引理。设原配置中的点 $P$ 与非空点集 $U$ 满足：

* $P\notin U$，$U$ 每个点都是原 hull light、类型 LI；
* 对 $u\in U$、$z\notin U\cup\{P\}$，有 $\angle uPz\ge3\lambda$。

对每个 $u\in U$，三角形角和给

\[
\angle Puz\le\pi-3\lambda<2\lambda.
\]

LI 行有唯一内 big gap 至少 $2\lambda$，分成两个实际端簇。因此每个这样的 $z$ 与 $P$ 都在 $u$ 的同一端簇；另一端只可能含 $U\setminus\{u\}$ 中的点。

这另一端非空，且全为 light。它不能 singleton：删除其唯一 light 点会合并外 gap 至少 $\lambda$ 与内 big gap 至少 $2\lambda$，使原 $\kappa=1$ 行增长、收费至少 $2$，违反该 light 的零总删除预算。所以另一端至少两点，$|U|\ge3$。

若 $|U|=3$，在每个 $u$ 处另外两点都在同一 LI 端簇，其夹角至多

\[
T=\pi-3\lambda<\pi/3.
\]

三角形 U 的三个角均严格小于 $\pi/3$，矛盾。因此

\[
\boxed{|U|\ge4.}
\]

没有最近邻、子凸包或多删假设。这个引理适用于 interior 的纯 LI apex，也适用于 HO 的任一纯 LI 端簇。允许 LI 含 heavy 的另一端 singleton；证明只禁止完全由 light 构成的这一端 singleton。

## 7. 排除 HM + LI6 + interior1

记 HM 为 B、interior 为 X。若 B 在 X apex，另外两个 nonapex runs 都只含 hull light，各至少两点。对这些至少四个 nonapex light H，X 处 $\angle BXH\ge3\lambda$，迫 B 处 X,H 同端。故 B 的这一端至少五条射线，反端至多两条且全为 light。

HM 两端均非 singleton，所以反端只能恰为两个 light；直接二删会清空保留 heavy 的端簇、收费至少四，超过二删预算二。故 B 不在 X apex。

于是 X apex 全为 LI hull light。第 6 节给至少四点。对其中每个 u，X 处 $\angle BXu\ge3\lambda$，迫 B 处 X,u 同端。该端至少五条，反端至多两条且全为 light，再由 heavy 非 singleton 与二删预算矛盾。

因此 HM 的最后一个八点分支闭合。这条证明直接使用原配置，不经过未知的五点 equality。

## 8. 排除 HA + LI5 + interior2

记唯一 heavy 为 A，两个 interior light 为 X,Y，五个 hull light 为集合 H。

### 8.1 每个 interior apex 必含 A 或另一个 interior

若 X apex 只含 hull light，第 6 节给至少四点。Y 在 apex 外。对其中每个 u，X 处 $\angle YXu\ge3\lambda$，迫 Y 处 X,u 同 run。Y 的这一 run 至少五条；它总共七条射线，剩余至多 A 与一个 light，无法填满另外两个非空 runs而不产生 light singleton。矛盾。

因此 X apex 含 A 或 Y；Y apex 含 A 或 X。

### 8.2 不可能完全不互含，亦不可能单向互含

若 Y 不在 X apex、X 不在 Y apex，两 apex 都含 A，三角形 AXY 在 X,Y 的两个角都至少 $3\lambda$，矛盾。

设单向互含：Y 在 X apex、X 不在 Y apex。Y apex 因而含 A。Y 处 $\angle XYA\ge3\lambda$，迫 X 处 Y,A 同 run，所以 A 也在 X apex。

X 的另两个 runs 全部由 hull light 填充，各至少两点，所以 X apex 外至少有四个 hull light。对每个这种 H，X 处 $\angle YXH\ge3\lambda$，迫 Y 处 X,H 同 run。这个 Y run 至少五条；Y apex 又含 A，至多剩一个 light 用来填第三个 run，产生空 run 或 forbidden light singleton。对称的单向互含也不可能。

### 8.3 相互包含时的 active partition 矛盾

剩下 Y 在 X apex、X 在 Y apex。定义

\[
U=(X\text{ apex})\setminus\{Y\},\qquad
V=(Y\text{ apex})\setminus\{X\},
\qquad D=\{A\}\cup H,\quad |D|=6.
\]

U,V 非空，因为单个 light Y 或 X 不能单独占一个 run。

若 h 同时属于 U,V，三角形 hXY 在 X,Y 的两个角都至多 R，迫第三角超过 $\pi-\lambda$。所以 U,V 不交。

若某 h 属于 D 却不在 U,V 中，三角形 hXY 在 X,Y 的两个角都至少 $3\lambda$，亦不可能。因此 U,V 恰分割 D。

设 A 在 U。X 的两个 nonapex runs 全由 V 中的 light 填充，所以 $|V|\ge4$。Y 的两个 nonapex runs 由 U 填充；只有 A 可能 singleton，另一全 light run 至少两点，所以 $|U|\ge3$。于是

\[
6=|U|+|V|\ge7,
\]

矛盾。A 在 V 时对称。

因此 HA 的最后八点分支闭合。此证明不需要 HA 的最近邻互向条件，也没有删除任何点。

## 9. 排除 allHull HO + LI7

HO B 的七个 light 分成两个实际端簇 S,T，跨簇角至少 $3\lambda$。对 P=B、U=S 应用第 6 节，得 $|S|\ge4$；同理 $|T|\ge4$。因此

\[
7=|S|+|T|\ge8,
\]

矛盾。

这里没有把删除后五点 F16 equality 当作不可能；证明全在原八点配置，使用 retained LI 行的原零 light 删除预算。

## 10. 五点 F16 的显式实际负控

一个容易造成假闭合的命题是：“一个 $\kappa3$ hull 点加四个 $\kappa1$ LI 点不能实际实现 F16。”这个命题的全 hull 版本为假。

取

\[
\lambda=\frac{7\pi}{30},\qquad R=\frac{\pi}{15},
\]

以及严格凸五边形，按 hull 顺序

\[
B=(0,-1000),\quad U=(-50,0),\quad V=(-49,1),\quad
W=(49,1),\quad Z=(50,0).
\]

令

\[
a=\arctan(1/20),\quad b=\arctan(49/1001),\quad
c=\arctan(1/99).
\]

有 $0<b<a<\pi/30$，且
$b+c<1/20+1/99<1/10<\pi/30$。实际 hull 内角为

\[
\alpha_B=2a<R,\qquad
\alpha_U=\alpha_Z=3\pi/4-a,\qquad
\alpha_V=\alpha_W=3\pi/4.
\]

所以所有实际三角角均至多 $3\pi/4<\pi-\lambda$。五点真实 projective gap 多重集为

| 点 | gaps |
|---|---|
| B | $a-b,\ 2b,\ a-b,\ \pi-2a$ |
| U,Z | $\pi/2-a,\ c,\ \pi/4-c,\ \pi/4+a$ |
| V,W | $\pi/4+b,\ \pi/2-b-c,\ c,\ \pi/4$ |

B 的唯一 big gap 严格大于 $4\lambda$、小于 $5\lambda$，故 $\kappa_B=3$。其余四点唯一内部 big gap 严格位于 $(2\lambda,3\lambda)$，其他 gaps 小于 $2\lambda$，故均为 $\kappa=1$。它们的 exterior gaps 为 $\pi/4+a$ 或 $\pi/4$，属于 $[\lambda,2\lambda)$，所以全为 LI。

因此 $8+4\cdot2=16$ 确实实现。它没有原 critical 配置的所有 light 零删除关系；第 6 节的隔离块结论不能无条件搬到这个五点 equality。本文最终排除始终使用原 counter 的零 light 删除预算，未假设未知 equality 分类。

## 11. 结论与范围

第 2–5 节排除所有较小 hull 或错误 heavy 类型；第 7–9 节排除仅剩三个模式。因此

\[
\boxed{\text{F18 的全部 }t=1,N=8\text{ 分支已在纸面闭合。}}
\]

与已冻结的六点、七点证明及独立九点证明合并，可用于完整 F18 PAPER 关闭。本文件本身不承担九点证明，也不声称三 run/apex 的 Lean 形式化已经完成。
