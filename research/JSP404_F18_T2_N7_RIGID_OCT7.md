# F18：七点 HM2 分支的 rigid 三角形排除

日期：2026-10-07。状态：实际配置纸面证明；没有 Lean、构建、Git 操作。接续冻结稿，不修改旧文件：

* [四顶点七点证明](JSP404_F18_T2_N7_OCT7.md)；
* [七点全部 HO 排除](JSP404_F18_T2_N7_HO_OCT7.md)。

固定 minimal actual F18 counter，$2\pi/9<\lambda\le\pi/4$，$R=\pi-4\lambda<\lambda/2$，$N=7,t=2,L=5$。每个 light 单删预算零，heavy 单删预算 $2$，直接二删 light 的累计预算 $2$。

## 1. Rigid 三角形的准确规律

Rigid 指原 HM/HO heavy 或原 interior light。任意 rigid 中心观察两点的角要么至多 $R$，要么至少 $2\lambda$。

任意三个 rigid 构成的实际三角形：

* 不可能有两个 small 角，否则角和至多 $2R<\lambda$，第三角超过合法上界 $\pi-\lambda$；
* 不可能三个角都 large，否则角和至少 $6\lambda>\pi$；
* 因此恰一个 small 角、两个 large 角；
* 任何一个 large 角都不能达到 $3\lambda$，否则它与另一个 large 角之和至少 $5\lambda>\pi$。

在 interior light 的三个 runs 中，apex 与任一 nonapex 夹角至少 $3\lambda$。故任意其他两个 rigid 不能一个在 apex、另一个在 nonapex。

下面也使用：所有 HM 不能成为任何点的最近邻；interior light 不能成为 light 的最近邻；light 射线在 interior 行不能 singleton。它们来自原 single-delete debt 与真实半尺度 witness，不是子集附加假设。

## 2. 排除五顶点 fullHull：HM2 + hull light3 + interior light2

记 HM 为 $B,C$，interior light 为 $X,Y$，hull light 集为 $H$，$|H|=3$。对 $X$，其他三个 rigid $B,C,Y$ 不能跨 apex/nonapex，因此要么全在 apex，要么全在两个 nonapex runs。

若全在 apex，剩余三个 hull light 需要填满另外两个非空 runs；各 run 不能 light singleton，至少需要四点，矛盾。

所以 $B,C,Y$ 全部 nonapex。$X$ 的 apex 只有 hull light，且至少两点。对 $Y$ 同理，其 apex 至少含两个 hull light，而 $B,C,X$ 全部 nonapex。

两个至少二点的 apex 子集取自同一个三点集 $H$，必共享某点 $Q$。于是三角形 $QXY$ 满足

\[
\angle QXY\ge3\lambda,\qquad
\angle QYX\ge3\lambda,
\]

两角和超过 $\pi$，矛盾。这里没有删除后凸包论证，也不依赖 hull light 是 LB 还是 LI。

## 3. 排除六顶点 fullHull：HM2 + hull light4 + interior light1

记 HM 为 $B,C$，唯一 interior light 为 $X$，四个 hull light 为集合 $H$。此时由转角预算它们都是 LI，但以下证明只需它们为 light。

由第 1 节，$B,C$ 不能跨 $X$ 的 apex/nonapex。分三种情形。

### 3.1 两 HM 都在 apex

另外两个 runs 只能由四个 hull light 填满，每 run 至少两点，因此 apex 恰为 $\{B,C\}$，其余是两个 light 二点 runs。

同 apex 角至多 $R<\lambda/2$，真实三角形度量比较双向给

\[
BC<BX,\qquad BC<CX.
\]

对任意 hull light $Q$，$B,Q$ 在 $X$ 的 apex/nonapex 两侧，故 $\angle BXQ\ge3\lambda>\pi/2$，给 $BQ>BX$。于是 $C$ 比 $X$ 及每个 hull light 都严格更近于 $B$，它成为 $B$ 的唯一最近邻，违背 HM 不能成为任何点最近邻。

### 3.2 两 HM 在同一个 nonapex run

此时 $\angle BXC\le R$，rigid 三角形规律迫 $\angle CBX,\angle BCX\ge2\lambda$。因此在 $B$ 的两端簇，$C,X$ 异端；在 $C$ 的两端簇，$B,X$ 异端。

设 $X$ 的 apex 含 $a$ 个 hull light，$a\ge2$。对任一 apex light $Q$，$\angle BXQ\ge3\lambda$，所以 $B$ 处 $X,Q$ 不能异端（否则另外至少 $2\lambda$），必须同端。对 $C$ 同理。

两 HM 的另一端各含另一个 heavy，并须至少再含一个 leftover hull light，否则为 forbidden singleton。故 $a\le3$。

若 $a=3$，唯一 leftover light $S$ 必在 $B$ 端与 $C$ 同簇、在 $C$ 端与 $B$ 同簇。因此

\[
\angle SBC\le R,\qquad\angle SCB\le R,
\]

第三角超过 $\pi-\lambda$，矛盾。

若 $a=2$，记 apex pair 为 $Q,R$，leftover pair 为 $S,T$。由于 $B,C$ 占同一个 nonapex run，$S,T$ 恰占另一个 nonapex run。

同 run pair 距离严格小于两端各自到 $X$ 的距离。两 light pairs 跨 apex/nonapex 的角至少 $3\lambda>\pi/2$，跨 pair 的距离大于对应点到 $X$ 的距离。HM 及 $X$ 又不能承接 light 最近邻，所以

\[
Q\leftrightarrow R,\qquad S\leftrightarrow T.
\]

Mutual pair 在任何第三中心角至多 $\pi/3<2\lambda$，因此 $S,T$ 不能被任一 HM 拆到两端。各 HM 的 other-heavy 端需要一个 leftover light，故事实上 $S,T$ 在 $B$ 均随 $C$，在 $C$ 均随 $B$。取 $S$，再次得到上面的两个 small 角，矛盾。

### 3.3 两 HM 分居两个 nonapex runs

此时 $\angle BXC\ge2\lambda$。Rigid 三角形只有一个 small 角，它必须在某个 heavy，设为 $B$，所以 $C,X$ 在 $B$ 同一端簇。

$X$ 的 apex 至少含两个 hull light。与 3.2 同样的 $3\lambda+2\lambda$ 三角形排除表明，全部 apex light 在 $B$ 都与 $X$ 同端。故该端包含

\[
\{C,X\}\cup\{\text{至少两个 apex light}\},
\]

至少四点。$B$ 总共有六条射线，另一端至多两点，并且只能是 hull light。两端非 singleton 迫该端恰由两个 light 组成。

直接删除这两个原 light 会清空保留 heavy $B$ 的整个端簇，使其 score 增长至少 $1$、收费 $4$，超过二删预算 $2$，矛盾。

## 4. 当前七点残余

上述三种情形穷尽，故 $N=7$ 的 HM2 + LI4 + interior1 分支也已纸面闭合。

结合原四顶点证明、全部 HO 证明与本 note，七点两 heavy 的唯一仍未排除类型为

\[
\boxed{\text{fullHull pentagon: HA + HM + LI3,\quad interior light2}.}
\]

此结论仍只是实际 counter 的必要剩余。八点、九点分支仍未闭合。本 note 没有从一次删除后重新套原 critical debt，也未使用未知 equality 分类。
