# ActualPureLightBlock：原 F18 的纯 light 分离块

日期：2026-10-07。初稿按 SOURCE_ONLY 交付；随后 Root 明确授予唯一检查 slot，两个公开消费者已通过 strict 和 genuine normal。未运行 Git 或 quota 检查。

新增来源为 [ActualPureLightBlock.lean](../Jsp000404/ActualPureLightBlock.lean)。数学来源编辑限于此新模块和本新 note；核验另产生专属 verification 收据。没有改旧冻结纸面稿或其他人的来源。

## 实际消费者接口

公开定理为 $\texttt{actual\_F18\_pure\_light\_block\_card\_ge\_four}$。

它只接受原实际 cap-16 minimum model、原 potential $F=18$、真实非空 Finset $U$、原点 $p\notin U$、每个 $u\in U$ 的原 fullHull 身份及原 score $1$，以及

\[
\forall u\in U\ \forall v\notin U,\quad
v\ne p\Longrightarrow\angle upv\ge3\lambda.
\]

模型自身固定 $2\pi/9<\lambda\le\pi/4$。接口不接收 window、clump、gain、budget 或删除后 hull 证书。$v=p$ 的排除在公开前提中明写，证明单独处理这个点，不对它套三角大角条件。

## 纸面短链与源码对应

对每个原 hull light $u\in U$，现有实际生产器
$\texttt{ActualF18LightHullClumps.exists\_actual\_F18\_hull\_light\_clumps}$
内部给出 LI 两 clumps，异 clump 角至少 $2\lambda$，同 clump 角至多

\[
T=\pi-3\lambda<\pi/3.
\]

每个 $U$ 外的 $v\ne p$ 在 $p$ 处与 $u$ 的角至少为 $3\lambda$。若 $v,p$ 在 $u$ 的异 clump，另有一个至少 $2\lambda$ 的角，违反 $5\lambda>\pi$。故所有 $U$ 外点都在 $u$ 的含 $p$ clump；另一 clump 只含 $U\setminus\{u\}$，因而是纯 light。

源码只为原 light target 证明 companion。若纯 light clump 是 singleton $q$，每个另外的原射线与 $q$ 异 clump，角至少 $2\lambda\ge\lambda$，现有实际 emission 定理
$\texttt{rowGain\_pos\_of\_forall\_angle\_ge}$
给出在原 observer $u$ 删除原 target $q$ 的 gain 至少为 $1$。这与
$\texttt{ActualInteriorOneClassSize.actual\_low\_four\_F18\_light\_incoming\_gain\_zero}$
矛盾。此 zero-gain 定理的 observer 任意，只有 target $q$ 必须原 score 为 $1$。

因此，每个 $u\in U$ 的另一 clump 至少给出两个不同的原 light 点 $q,r\in U\setminus\{u\}$，两者在 $u$ 处夹角至多为 $T$。先得 $|U|\ge3$。若 $|U|\le3$，这两个点穷尽 $U\setminus\{u\}$；在三点的每个顶点都得到对应夹角至多为 $T<\pi/3$。三个角之和小于 $\pi$，矛盾。因此

\[
\boxed{|U|\ge4}.
\]

## 纯 light 边界与核验范围

没有声称任意原 LI clump 都至少两点。含 heavy singleton 的 clump 仍被允许；这里用于 emission contradiction 的 clump 之所以纯 light，仅由 $U$ 的原 score-one 支持条件和 outside-clump 排除推出。

模块尾部列出两个公开消费者的 axioms 检查命令。初稿只有静态读取与 API 来源核对；后续正式授权的实际检查记录见下节。这些结果只覆盖本模块的两个 selected 消费者，不声称全部 F18 或全项目证明闭合。

## allHull、唯一 heavy 的 HO 消费者

后续同文件新增
$\texttt{actual\_F18\_one\_heavy\_all\_hull\_three\_scale\_angle\_false}$，
原 block 定理的数学证明保持不变。

新消费者接受原 Model/F18、一个原 score-two 点 $p$、所有其余点的原 HullLight 支持，以及在 $p$ 处一个实际角至少为 $3\lambda$。它不接受 HO 分类、clump、点数或较低 cap 证书。

内部先由原 F18 frame 和唯一 heavy 得到原点数 $8$。实际 hull-two Types 生产器给出 $p$ 的类型：HA 的 full cone 至多 $\pi-3\lambda<3\lambda$，HM 的 full cone 至多 $\pi-2\lambda<3\lambda$，均与实际角前提冲突，故只余 HO。

HO 内部产生的两个非空端 clumps 异端角至少为 $3\lambda$；两端全为原 HullLight。把各端分别作为实际 Finset $U$，上面的纯 light block 消费者各给至少四点。两个端纤维完整分割除 $p$ 外的原七点，却合计至少八点，矛盾。

此消费者与 block 定理在同一最终来源上完成了下面的实际核验。

## 正式授权后的检查收据

最终来源 SHA256：
$\texttt{c5ec723c52eec0167da55f52b60d5027dbe9f73a25cee63dab569e677414759c}$。

选定公开名单：

* $\texttt{Jsp404.ActualPureLightBlock.actual\_F18\_pure\_light\_block\_card\_ge\_four}$；
* $\texttt{Jsp404.ActualPureLightBlock.actual\_F18\_one\_heavy\_all\_hull\_three\_scale\_angle\_false}$。

统一 [guarded driver](../verification/oct7-actual-pure-light-block/check.py) 在每次启动前排除其他 Lean，并在运行期间每 100 ms 检查进程树 RSS、180 秒时限和全局最多一个 Lean。RSS cap 为 8 GiB。

| 阶段 | 实际状态 | exit | 秒数 | peak tree RSS KiB |
|---|---|---:|---:|---:|
| strict attempt01 | FAIL，已保留 | 1 | 13.1063 | 6364272 |
| strict attempt02 | PASS | 0 | 20.6442 | 6442272 |
| genuine normal attempt01 | PASS | 0 | 16.8877 | 6442016 |

首次失败是三点 Finset helper 在 case substitution 后引用已被消去的局部变量名。只修复该 angle-symmetry 表达，数学论证未变；失败的 [exact source](../verification/oct7-actual-pure-light-block/strict-attempt01.source.lean) 与 [raw stdout](../verification/oct7-actual-pure-light-block/strict-attempt01.stdout.txt) 保留，未覆盖。

最终 [strict raw](../verification/oct7-actual-pure-light-block/strict-attempt02.stdout.txt) 和 [normal raw](../verification/oct7-actual-pure-light-block/normal-attempt01.stdout.txt) 的两个 selected 都仅依赖 $\texttt{propext, Classical.choice, Quot.sound}$。normal 日志实际包含 own-module Built 和 Build completed successfully；未把 replay 当成 own-module build。

[checkpoint.json](../verification/oct7-actual-pure-light-block/checkpoint.json) 记录每轮 exact source、raw、来源 SHA、artifact SHA、资源状态与 selected axioms。正常阶段与 strict PASS 使用同一来源 SHA；两次 PASS 都无 resource stop。normal 结束后已立即向 Root 正式 release 唯一 heavy slot。
