# 两公共坐标投影的有限权重界

**PASS**：`Jsp404.TwoCoordinatePacking.two_coordinate_weighted_bound` 已真实
`--trust=0`、exit 0 检查通过，仅依赖 `propext`、`Classical.choice`、
`Quot.sound`，无 warning。源码 `Jsp000404/TwoCoordinatePacking.lean`（108 行），SHA256：

`87e4a20816b75b48f95ad1da45a614f37152b0e08ebcd391e9f42d9c8a25bb31`

任意有限顶点 V，输入 fullSpecified 与 Boolean bit。两个不同坐标 ka/kb
在每个顶点的指定集中；任意两个不同顶点，能在非 ka/kb 的双方指定坐标上
以不同 bit 分离；每个局部指数 ks_v≤n−|fullSpecified_v|。结论为
`Σ_v 2^ks_v≤2^(n−2)`。

源码在内部取 univ\{ka,kb}，用 orderEmbOfFin 构造 Fin(n−2) 到剩余坐标
的枚举和满射，证明每个重标指定集大小恰为旧大小−2，再调用既有、保留
归属的 `ThirdParty/Sendov/JSP404/BinaryEncoding.lean` 计数定理。没有
aggregate mass、物理 n−2 区间或原题极值定义重命名的前提。

实际检查命令：

```text
lake env lean --trust=0 -o .lake/build/lib/lean/Jsp000404/TwoCoordinatePacking.olean Jsp000404/TwoCoordinatePacking.lean
```

`/usr/bin/time -l`：real 4.85 秒，最高 RSS 3,038,937,088 bytes（2.830 GiB），
peak memory footprint 137,798,312 bytes（约 131 MiB），低于单 scope 3.5 GiB
授权门槛。初次检查的 API 错误在源中普通修复，未将错误恢复的输出计为
证明；最终源码已通过。没有 normal Lake/fullbuild。

这只是通用 finite graph/Boolean packing 定理。纸面
`JSP404_R2_UNIFORM_TAIL_ROUTE_20261005.md` 的 actual BETWEEN 接口仍为
**CONDITIONAL**：几何调用者还须真正建立两公共指定坐标及 remaining
separator。共享低低 bin、ABOVE/BELOW 同另色情形仍未排除；不能据此
声称全 R2 或原题全 N 已闭合。旧 N3、十一点、root imports、audit、Git
均未修改。
