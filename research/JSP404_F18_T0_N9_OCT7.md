# F18：九点全 light 的最后两个 hull 分支

日期：2026-10-07。状态：actual 几何纸面证明；没有 Lean PASS、构建或全部 F18 完成声明。

本文只排除 $t=0,N=9$ 剩余的 $I=2,h=7$ 与 $I=1,h=8$。所有 hull、interior、run、clump 都指原九点配置。证明不删除任何点，不推断子集凸包，也不重新套用中间配置的 critical debt。

## 1. 原配置事实与两个基本引理

固定 minimal actual F18 counter，九点全为权重 $2$ 的 light，且

\[
\frac{2\pi}{9}<\lambda\le\frac{\pi}{4},\qquad
R=\pi-4\lambda<\frac{\lambda}{2},\qquad
T=\pi-3\lambda<\frac{\pi}{3}.
\]

于是 $2R<\lambda$、$R<2\lambda$、$2\lambda>\pi/3$、$3\lambda>\pi/2$、$5\lambda>\pi$、$6\lambda>\pi$。原配置无三点共线，每个实际三角形角均不超过 $\pi-\lambda$。

使用已经由原 single-delete zero-gain 得到的结构：

* 每个原 interior 点有三个非空实际 runs，每个至少含两条射线。总宽至多 $R$，同 run 角至多 $R$，异 run 角至少 $2\lambda$。唯一 apex run 与每一个另外的 run 之间，所有实际夹角至少 $3\lambda$。
* 每个原 hull 点为 LI，其实际射线分为两个端 clumps。每个 clump 至少含两点，宽至多 $T$；异 clump 角至少 $2\lambda$。

端 clump 至少两点和 interior run 至少两点这两个输入本身使用原单删 debt。下文在这些原配置事实基础上，不追加多删预算或未知 equality 分类。

### 1.1 大角传递

设 $P,C,Z$ 是三个实际点，且 $P$ 是这里的一个 interior 或 LI hull 中心。若

\[
\angle PCZ\ge3\lambda,
\]

则 $C,Z$ 在 $P$ 的同一 run 或同一 LI clump。否则 $P$ 处还有一个至少 $2\lambda$ 的角，两角之和至少为 $5\lambda>\pi$。

### 1.2 Small 角的严格距离比较

在任意实际三角形中，若一个角 $\theta\le R$，则任一个另外的角 $\phi$ 都满足

\[
\phi\ge\lambda-\theta\ge\lambda-R>R\ge\theta.
\]

这里使用第三角的上界 $\pi-\lambda$ 和 $2R<\lambda$。因此，small 角所对的边严格短于另外两边。特别地，同一个 interior run 内的任意两点 $P,Q$ 满足

\[
PQ<XP,\qquad PQ<XQ.
\]

以上比较均严格，不受最近邻距离 ties 影响。

## 2. 两 interior：另一个 interior 不能在 apex

现在 $h=7,I=2$。原 hull light 集为 $H$，$|H|=7$，两个 interior 点为 $X,Y$。

假设 $Y$ 在 $X$ 的 apex。$X$ 的两个 nonapex runs 全由 hull light 组成，各至少两点，合计至少四点。对其中任一点 $z$，

\[
\angle YXz\ge3\lambda.
\]

传递到 $Y$ 得 $X,z$ 同 run。因此 $Y$ 的一个 run 至少含 $X$ 加四个 hull light，共至少五点；另外两个 runs 各至少两点，总计至少九条射线。然而 $Y$ 只有八条实际射线，矛盾。

交换 $X,Y$ 同理。故 $Y$ 在 $X$ 的 nonapex，$X$ 在 $Y$ 的 nonapex。

令 $U,V\subset H$ 分别为 $X,Y$ 的 apex 点集。它们各至少两点。如果 $z\in U\cap V$，三角形 $XYz$ 在 $X,Y$ 两处的角都至少为 $3\lambda$，矛盾。因此

\[
U\cap V=\varnothing,\qquad |U|,|V|\ge2.
\]

记 $W=H\setminus(U\cup V)$，故 $|W|\le3$。大角传递还给出：

* $V$ 全部在 $X$ 的含 $Y$ nonapex run；
* $U$ 全部在 $Y$ 的含 $X$ nonapex run。

令 $T_X$ 为 $X$ 的另一个 nonapex run 的点集，$T_Y$ 为 $Y$ 的另一个 nonapex run 的点集。则

\[
T_X,T_Y\subset W,\qquad |T_X|,|T_Y|\ge2.
\]

这里 $T_X,T_Y$ 是点集，宽度常数仍记为 $T$。

若 $w\in W\setminus(T_X\cup T_Y)$，则 $w$ 在 $X$ 与 $Y$ 同 run、在 $Y$ 与 $X$ 同 run，三角形 $XYw$ 有两个角至多为 $R$。第三角至少为 $\pi-2R>\pi-\lambda$，非法。所以

\[
T_X\cup T_Y=W.
\]

## 3. 两 interior：三个 leftover hull light

因为 $|W|\le3$ 而 $|T_X|,|T_Y|\ge2$，交集 $Z=T_X\cap T_Y$ 非空。任取 $z\in Z$。在三角形 $XYz$，$X,Y$ 两处的角各至少为 $2\lambda$，故

\[
\angle XzY\le\pi-4\lambda=R.
\]

于是 $X,Y$ 在 LI 中心 $z$ 的同一 clump。大角传递分别把 $U$ 与 $X$、$V$ 与 $Y$ 放入该 clump，因此它包含

\[
\{X,Y\}\cup U\cup V.
\]

$z$ 的另一 clump 至少需两点，而剩余候选只有 $W\setminus\{z\}$。所以 $|W|\ge3$。结合上一节，得到精确基数

\[
|W|=3,\qquad |U|=|V|=2.
\]

对每一个 $z\in Z$，其另一个 clump 恰为 $W\setminus\{z\}$；特别地，原三角形 $W$ 在 $z$ 处的角至多为 $T$。

若 $|Z|\ge2$：

* 当 $Z=W$ 时，三角形 $W$ 的三个角均至多为 $T<\pi/3$，矛盾。
* 当 $|Z|=2$ 时，记 $W\setminus Z=\{p\}$。例如 $p\notin T_X$；若缺的是 $T_Y$，对称处理。对每个 $z\in Z$，在三角形 $Xpz$，$X$ 处的 $p,z$ 异 run，$z$ 处的 $X,p$ 异 clump，因此两角各至少为 $2\lambda$，故 $\angle Xpz\le R$。两个 $Z$ 点在 $p$ 的同一 LI clump，三角形 $W$ 在 $p$ 处的角也至多为 $T$。连同两个 $Z$ 顶点，又得到三个角都小于 $\pi/3$ 的矛盾。

故唯一尚需检查的模式是

\[
W=\{z,p,q\},\qquad T_X=\{z,p\},\qquad T_Y=\{z,q\}.
\]

## 4. 两 interior：最后模式产生严格短边循环

在三角形 $Yzp$，$Y$ 处的 $z,p$ 异 run，$z$ 处的 $Y,p$ 异 clump，所以

\[
\angle Ypz\le R.
\]

因此 $Y,z$ 在 $p$ 的同一 LI clump。对称地，$X,z$ 在 $q$ 的同一 clump。

在 $p$，大角传递给 $X,U$ 同 clump、$Y,V$ 同 clump。如果 $X,Y$ 也同 clump，该 clump 将包含

\[
\{X,Y,z\}\cup U\cup V
\]

共七条射线，另一 clump 只剩 $q$，违反至少两点。因此 $X,Y$ 在 $p$ 的不同 clumps。同理它们在 $q$ 的不同 clumps。

于是 $p$ 处含 $z$ 的是 $Y$-clump，$q$ 处含 $z$ 的是 $X$-clump。若 $q$ 在 $p$ 随 $z$、同时 $p$ 在 $q$ 随 $z$，三角形 $W$ 的三个角均至多为 $T<\pi/3$，矛盾。

交换 $X,Y$ 及 $p,q$ 后，可设 $q$ 在 $p$ 的 $X$-clump。则 $\angle Ypq\ge2\lambda$；$Y$ 处的 $p,q$ 也异 run，所以三角形 $Ypq$ 给

\[
\angle Yqp\le R.
\]

故 $p$ 在 $q$ 的 $Y$-clump，与 $q$ 的 $X$-clump 不同，因而 $\angle Xqp\ge2\lambda$。$X$ 处的 $p,q$ 也异 run，三角形 $Xpq$ 给

\[
\angle Xpq\le R.
\]

此外，$p\notin T_Y$、$q\notin T_X$ 给

\[
\angle XYp\le R,\qquad \angle YXq\le R.
\]

把第 1.2 节的严格短边比较依次用于这四个 small 角，得到

\[
Xq<Xp<Yp<Yq<Xq,
\]

不可能。因此 $t=0,N=9,I=2,h=7$ 的实际配置不存在。

## 5. 一 interior：apex 被迫为四点

现在 $h=8,I=1$，唯一原 interior 点为 $X$。记其三个 runs 为 apex $U$ 与两个 nonapex runs $V,W$，它们都是原 hull light 点集，且各至少两点。

对任意 $u\in U$ 和 $z\notin U$，在 $X$ 有

\[
\angle uXz\ge3\lambda.
\]

大角传递同时适用于三角形的另外两个顶点。因此，在每个 $u\in U$，$X$ 与全部 $U$ 外 hull 点同 LI clump；在每个 $z\notin U$，$X$ 与全部 $U$ 点同 LI clump。

特别地，在 $u$ 的另一 clump 中只能出现 $U\setminus\{u\}$。该 clump 至少两点，故 $|U|\ge3$。若 $|U|=3$，三个 $U$ 顶点都把另外两个 $U$ 点放在同一个 clump，三角形 $U$ 的三个角均至多为 $T<\pi/3$，矛盾。

所以 $|U|\ge4$。又因另外两个 runs 各至少两点，八个 hull 点只能按

\[
|U|=4,\qquad |V|=|W|=2
\]

分配。

## 6. 一 interior：较近的二点 run 是严格 mutual nearest pair

在 $V\cup W$ 中选择到 $X$ 距离最小的一点，重命名为 $w\in W$。写

\[
W=\{w,w'\},\qquad r_P=XP,\qquad d=ww'.
\]

第 1.2 节给

\[
d<r_w,\qquad d<r_{w'},\qquad
r_{w'}\le r_w+d<2r_w.
\]

对任意 $v\in V$，有 $r_v\ge r_w$，且 $\theta=\angle wXv\ge2\lambda>\pi/3$。由余弦定理，

\[
wv^2-r_w^2
=r_v(r_v-2r_w\cos\theta)>0.
\]

所以 $wv>r_w>d$。对任意 $u\in U$，$\angle wXu\ge3\lambda>\pi/2$，所以 $wu>r_w>d$；$X$ 本身与 $w$ 的距离也大于 $d$。因此 $w'$ 是 $w$ 的唯一最近邻。

还需严格核对反向，不能由单向最近邻直接声称 mutual。固定 $v\in V$，令

\[
\theta'=\angle w'Xv\ge2\lambda,\qquad
\delta=\angle w'Xw\le R.
\]

因为 $r_{w'}<2r_w$ 且 $\cos\theta'<1/2$，有 $r_{w'}\cos\theta'<r_w$。余弦定理给

\[
\begin{aligned}
w'v^2-d^2
={}&(r_v-r_w)
       (r_v+r_w-2r_{w'}\cos\theta')\\
&+2r_{w'}r_w(\cos\delta-\cos\theta')>0.
\end{aligned}
\]

第一项非负，第二项严格为正，因为 $\delta\le R<2\lambda\le\theta'$。对 $u\in U$，同样由 obtuse 的 apex/nonapex 角得 $w'u>r_{w'}>d$，而 $w'X=r_{w'}>d$。故 $w$ 也是 $w'$ 的唯一最近邻。

由此 $\{w,w'\}$ 是原九点配置的严格 mutual nearest pair。选择最小半径点时可以任意处理并列；上面所有最终最近邻比较严格，故结论保留距离 ties。

## 7. 一 interior：mutual pair 迫出 forbidden singleton

任意 mutual nearest pair 在任何第三中心的夹角至多为 $\pi/3$：在对应三角形中，pair 边不长于另外两边，所以它的对角是最小角。由于 LI 异 clump 角至少为 $2\lambda>\pi/3$，$w,w'$ 在任何 $v\in V$ 的同一 LI clump。

在这样的 $v$，第 5 节给 $X$ 与四个 $U$ 点同 clump。若二点 pair $W$ 也在这个 clump，该 clump 就包含

\[
\{X\}\cup U\cup W
\]

共七条射线，另一 clump 仅剩 $V$ 的另一个点，非法。因此 $W$ 的两点都在 $v$ 的另一 clump。于是对所有 $v\in V,w_0\in W$，

\[
\angle Xvw_0\ge2\lambda.
\]

而在 $X$，$V,W$ 异 run，故 $\angle vXw_0\ge2\lambda$。三角形 $Xvw_0$ 给

\[
\angle Xw_0v\le\pi-4\lambda=R.
\]

所以在每个 $w_0\in W$，$X$ 与全部 $V$ 点同 LI clump。第 5 节又把全部 $U$ 点加入同一 clump。这个 clump 包含

\[
\{X\}\cup U\cup V
\]

共七条射线，另一 clump 只有 $W\setminus\{w_0\}$ 的一个点，再次违反每个 LI clump 至少两点。

故 $t=0,N=9,I=1,h=8$ 的实际配置也不存在。

## 8. 结论范围

本文独立排除了原九点全 light 配置的两个最后分支：

\[
\boxed{I=2,h=7\quad\text{与}\quad I=1,h=8.}
\]

与已经核过的 $I=4,h=5$、$I=3,h=6$ rigid 分支，以及 $I=0,h=9$ 的曲率排除合并，才得到 $t=0,N=9$ 的纸面闭合。本文没有据此声称全部 F18、全部点数或 kernel 证明完成。

两个证明只使用原 actual 角界、原 runs/clumps 和原单删 debt 的结构后果。第二个证明构造了严格 mutual pair；没有假设一般最近邻 ties 消失，也没有把 generic weak SAT 的可行性或不可行性当作实际几何结论。
