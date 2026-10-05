# 压缩标量模型的 n′=3 终结适配

源码：`Jsp000404/N3SixModelTerminal.lean`。命名空间为
`Jsp404.N3SixModelTerminal`，`ModelSix3` 是
`SixModelCompression.ModelSix 3` 的别名。

该适配保留原模型的所有标量条件，将旧 `N3Model` 的参数取为
`lam=1`、`p=3+M.delta`、`t=M.theta`、`d=M.d`。周期界限由
`0≤delta<1` 给出，方向界限、corridor 和 triangle 直接来自原模型。

公开接口：

- `rowSig_of_linearScore_one`：任意实数周期 `p` 的四元素排序行，若
  `linearGapScore lam theta (theta+p) [...] = 1`，则满足
  `RowSig lam p theta ...`。不要求 `p=Real.pi`。
- `rowSig_of_rowDefect_eq_two`：从 `M.rowDefect i=2`、真实 `row_perm`、
  `row_sorted` 和 chord bounds 导出四元素排列及上述 signature。
- `row_one_defect_two_impossible`：`M.rowDefect 1=2` 导出 `False`。
- `row_three_defect_two_impossible`：`M.rowDefect 3=2` 导出 `False`。
- `endpoint_defects_two_impossible`：`M.rowDefect 0=2` 与
  `M.rowDefect 4=2` 同时成立时导出 `False`。

这里的 `rowDefect` 均为 `SixModelCompression.rowDefect`。`n=3` 时，
`3-score=2` 的自然数截断减法直接强制 `score=1`，因此此适配不需要
额外假设 score budget。四元素排列给出五个 primitive gaps；score
分类证明恰有一个 floor 等于 2，其余 floor 不超过 1。大 gap 的区间为
`[2*lam,3*lam)`，其余 gap 严格小于 `2*lam`。

下三角 chord 由 `M.symm` 转换后，结论分别消费旧 `n3_row1`、
`n3_row3` 和 `n3_between`。没有 `assumeSignature`，没有导入真实
`SatChart` 的任意两行几何分类，也没有把压缩标量数据声称为平面点。

验证状态：**PASS**。修复后的单 scope 实际执行：

```text
lake env lean --trust=0 -o .lake/build/lib/lean/Jsp000404/N3SixModelTerminal.olean Jsp000404/N3SixModelTerminal.lean
```

exit 0；五个公开声明全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`，
没有 warning、sorryAx、native 或自定义公理。最终源 SHA256：

`166e036b09363cc9a77a9d426ccedaaab165c06d1f98584b9e531cd392f18237`

运行 12.378 秒；观察最高 Lean RSS 为 6,058,967,040 bytes，系统
`/usr/bin/time -l` 最高 RSS 为 6,086,311,936 bytes（5.668 GiB），
peak memory footprint 为 137,962,200 bytes（约 132 MiB）。Root 对这个
单 scope 明确授权 8 GiB RSS，并暂停其他重型编译；没有 fullLake。

此前 2.5 GiB 与 4 GiB 门槛的尝试在导入阶段主动停止（exit 143），
没有计为 PASS。8 GiB 后首次源检验发现行上界中的 Nat `3` 转换为 Real
尚未正规化；加入 `norm_num only [Nat.cast_ofNat]` 后，最终检查通过。
这两个 imports 的大部分 RSS 来自依赖的映射页，而非 217 行适配源码。

公理输出对应声明：

```text
Jsp404.N3SixModelTerminal.rowSig_of_linearScore_one
Jsp404.N3SixModelTerminal.rowSig_of_rowDefect_eq_two
Jsp404.N3SixModelTerminal.row_one_defect_two_impossible
Jsp404.N3SixModelTerminal.row_three_defect_two_impossible
Jsp404.N3SixModelTerminal.endpoint_defects_two_impossible
```

当前没有本任务 Lean/Lake 进程继续运行。旧源码、冻结十一点证书、root
imports、审计和 Git 均未修改。这里只终结必要标量模型的指定行位置；
没有声称压缩坐标实际可由平面点实现，也没有单独证明任意两行排除。
