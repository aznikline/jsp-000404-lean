# Actual F18：全 light、唯一 interior 消费者

日期：2026-10-07。初稿为 SOURCE_ONLY；随后按 Root 正式授权的唯一 slot 完成 strict 与 genuine normal，两者实际 PASS。未运行 Git。

唯一新增数学来源为 [ActualF18SingleInterior.lean](../Jsp000404/ActualF18SingleInterior.lean)，公开入口为
$\texttt{actual\_F18\_all\_light\_single\_interior\_false}$。

入口只接收原 cap-16 minimal actual Model、原 $F=18$、每个原 score 都是 $1$、一个原 interior 点 $p$，以及其余每点的原 fullHull 身份。没有 caller 最近邻、clump、class cardinality、较低 cap 或 restricted Model 前提。

## 内部得到 $4+2+2$

原 F18 frame 与 all-light 前提给出原点数 $9$。在 $p$ 内部产生实际三类 partition，apex 是标签 $1$，其余标签为 $0,2$。原 light 单删零增益给每类至少两点。

将 apex 作为真实原 Finset，apex/nonapex 实际角至少为 $3\lambda$，所以已经核过的 ActualPureLightBlock 消费者给 apex 至少四点。三类完整分割其余八点，因此内部得到精确基数

\[
|U|=4,\qquad |V|=|W|=2.
\]

实际 class Finsets 由原 partition 的 subtype fiber 经原索引投影得到；没有沿用删除后的 hull 身份。

## 真实严格 mutual pair

只在两个 nonapex classes 的并集中，选到 $p$ 距离最小的一点 $w$。其二点类的另一成员为 $w'$。同类实际角至多 $R=\pi-4\lambda<\lambda/2$，实际合法角上界给

\[
d=ww'<r_w,\quad d<r_{w'},\quad
r_{w'}\le r_w+d<2r_w,\qquad r_x=px.
\]

对另一个 nonapex class 的任一点 $v$，$r_v\ge r_w$ 且在 $p$ 的夹角至少 $2\lambda>\pi/3$。余弦定理先给 $wv>r_w>d$。反向比较在来源内使用实际 cosine identity：

\[
\begin{aligned}
w'v^2-d^2={}&(r_v-r_w)
(r_v+r_w-2r_{w'}\cos\theta)\\
&+2r_{w'}r_w(\cos\delta-\cos\theta)>0,
\end{aligned}
\]

其中 $\theta\ge2\lambda$、$\delta\le R$。第一项非负，因为 $r_{w'}\cos\theta<r_w$；第二项严格正。

apex 点与 $w,w'$ 在 $p$ 处的夹角至少为 $3\lambda>\pi/2$，其距离严格大于对应半径。这个分支完全不需要 apex 半径有最小值。$p$ 本身也比 pair distance 更远。

因此，$w,w'$ 在全部原九点中互为唯一最近邻。没有预设 NN 关系；最小半径可有 ties，最终距离比较全部严格。

## 原 LI singleton 矛盾

任意第三中心观察该 mutual pair 的实际角至多为 $\pi/3<2\lambda$，所以 pair 在每个原 hull LI 中心的同一 clump。

在另一个 nonapex class 的 $v$ 处，$p$ 与全部 apex 点同 clump。若 mutual pair 也加入此 clump，除了 $v$ 的唯一 classmate 外，其余所有射线都同 clump。LI 的另一个 code witness 与原 light 目标的单删零增益排除这种 singleton。因此 pair 必须在 $v$ 的另一 clump。

这给三角形 $pvw$ 在 $p,v$ 两处的角均至少为 $2\lambda$，故在 $w$ 处的角至多为 $R$。于是，在 $w$ 处，$p$、全部 apex 点和另一个 nonapex class 全部同 LI clump，只剩 $w'$ 可能在另一 clump。再次由原 LI witness 和原 light 单删零增益得到 singleton 矛盾。

源码以“除一个 classmate 外全同 code”表述最后两次矛盾，无需把一个未证最近邻命题作为入口，也不把重排后的点集当作新 minimal counter。

## 当前核验边界

数学链与冻结的 N9 纸面 I1 分支一致，源码分解为实际角、实际距离、原 class Finset 和原零增益的私有 helpers。没有改动冻结 N9 笔记或其他人的模块。初稿静态交付后，Root 经 Low 正式 handoff 唯一检查 slot；下面记录该顺序核验。

## 正式核验收据

最终来源 SHA256：
$\texttt{3602563c6d66b080405b81ea4f9fbdfef999469c6a39d75494718c91193f1921}$。

唯一 selected public 为
$\texttt{Jsp404.ActualF18SingleInterior.actual\_F18\_all\_light\_single\_interior\_false}$。

[guarded driver](../verification/oct7-actual-f18-single-interior/check.py) 在每次启动前排除其他 Lean，并在运行期间每 100 ms 检查全局 Lean 数、进程树 RSS 和时限。上限是一个 Lean、8 GiB 与 180 秒。

| 阶段 | 状态 | exit | 秒数 | peak tree RSS KiB |
|---|---|---:|---:|---:|
| strict attempt01 | FAIL，保留原来源和 raw | 1 | 27.1046 | 6359760 |
| strict attempt02 | PASS | 0 | 18.8787 | 6421872 |
| genuine normal attempt01 | PASS | 0 | 19.9997 | 6341040 |

首次失败仅有 API 用法问题：三处 dist-nonneg 的端点是 implicit 参数，以及末支 apply 暴露的 hmin/hcover goals 顺序。只把前者写为 typed fact、后者写为显式 cover premise，数学和公开接口均未改。

失败的 [exact source](../verification/oct7-actual-f18-single-interior/strict-attempt01.source.lean) 与 [raw stdout](../verification/oct7-actual-f18-single-interior/strict-attempt01.stdout.txt) 已冻结保留。最终 [strict raw](../verification/oct7-actual-f18-single-interior/strict-attempt02.stdout.txt) 无 own warning；[normal raw](../verification/oct7-actual-f18-single-interior/normal-attempt01.stdout.txt) 实际包含 Built own module 与 Build completed successfully，也无本模块 own warning。selected 仅依赖 $\texttt{propext, Classical.choice, Quot.sound}$。

[checkpoint](../verification/oct7-actual-f18-single-interior/checkpoint.json) 记录每轮来源、raw、artifact 的 SHA256 与资源状态。normal 和 strict PASS 使用同一最终来源；两次 PASS 均无 resource stop。所有 Lean/Lake 退出后，已立即正式 return Root，并按授权 FOLLOWUP 归还 Low 检查加强后的 TwoInterior；没有重叠占用。

本收据只证明这个实际 I1 消费者，不独立声称整个 F18 或全项目闭合。
