# R1 归约审计回执 — `r1_n4_overcap_reduces`

**状态：SOURCE_CANDIDATE / STATIC_AUDIT_PENDING**（未记 PROVED）

日期：2026-10-12。分支 `agent/jsp404-air-emergency-owner-20260928`，
HEAD `9312176bfe01c0e37ecb22e81b079287e12da489`。

注：本文件审计的是拆分前的原始 `R1N4Capacity.lean`（HEAD 版本）。

**模块结构（契约保留版）**：
- `R1N4Delete.lean`：`R1N4Profile` + `R2N4OvercapExclusion` +
  `exists_tail` + `r1_tail_delete`（内部 helper，带 hr2）
- `R1N4Capacity.lean`：`r1_n4_overcap_reduces_of_r2_exclusion`
  （内部 helper，带 hr2）
- `R1N4Reduction.lean`：**原始无回调 API `r1_n4_overcap_reduces`，
  真实 wrapper**——内部以 `r2_n4_overcap_impossible` 供给 hr2，
  签名与 HEAD 版逐字一致。此模块传递 import R2 证书闭包（重），
  当前 **OPEN/待编译验证**——不得将 helper 版当作原始归约已关闭。

## 1. 声明（源码原文，`Jsp000404/R1N4Capacity.lean:459`）

```lean
theorem r1_n4_overcap_reduces :
    ∀ {t : ℕ} (_ht : 6 ≤ t) {lam : ℝ} (_hlam : 0 < lam)
      (_hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
      (_hleg : Section4Legality c lam) (_he : e ≠ 0),
      R1N4Profile o e lam c →
      2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c) →
      ∃ (T : ℕ) (c' : Fin T → Plane₂) (ι : Fin T ↪ Fin t),
        c' = c ∘ ⇑ι ∧ Section4Legality c' lam ∧
        R1N4Profile o e lam c' ∧
        ((T = 7 ∧ potential … = 22) ∨ (T = 7 ∧ … = 21) ∨
         (T = 8 ∧ … = 21) ∨ (T = 9 ∧ … = 21) ∨
         (T = 10 ∧ … = 21) ∨ (T = 11 ∧ … = 21))
```

归约保持 `c' = c ∘ ι` 真子嵌入与 `Section4Legality c' lam` 真合法性，
非重述假设。辅助：`r1_tail_delete`（`R1N4Capacity.lean:92`，private）。

## 2. olean ↔ 源码对应

- `.lake/build/lib/lean/Jsp000404/R1N4Capacity.olean` mtime 2026-10-10 16:42，
  由 `.trace` 记录的 `lean … -o …/R1N4Capacity.olean` 产出；
  trace 输入哈希 `ec4dd6898ea4b7f6`（lake 内部哈希）。
- 源码 mtime 2026-10-10 16:04，`git diff HEAD` 为空，`git log -1` =
  9312176 —— olean 对应当前已提交源码。
- 该 olean 产生于 unguarded `lake env lean`（当时记录 0 错误）。

## 3. 源码级审计

- `grep -nE 'sorry|admit|axiom|native_decide|unsafe' R1N4Capacity.lean`
  → 0 命中。文件内无新公理、无 sorry、无 native_decide。
- import 闭包：`R2N4Assembly` + `FivePointCapacity`。
  R2 链公理回执 `verification/r2-n4-final-axioms.txt`：
  `r2_n4_overcap_impossible` 等仅依赖 `[propext, Classical.choice,
  Quot.sound]`（标准三公理）。

## 4. 公理闭包 — **STATIC_AUDIT_PENDING（不得记 PROVED）**

组合静态论证**不构成**公理闭包证据：
- 源码无 sorry 仅证明本文件未直接引入公理，不代表传递闭包干净；
- `FivePointCapacity` 及其余实际调用链尚未做 `#print axioms` 核对；
- olean mtime 晚于源码只说明"之后构建过"，不是 fresh 编译证据。

待执行（守卫允许时）：对 `R1N4Delete` / `R1N4Capacity` 探针文件
`#print axioms r1_n4_overcap_reduces` 与 `#print axioms` 链上
实际调用定理逐一核对。

**阻塞记录**：`#print axioms` 探针
（`verification/r1-reduce-axioms.lean`）在守卫 4GiB RSS 下无法运行——
import 闭包的 mmap olean 加载即 4.2–4.3GB（守卫 JSON 见
`verification/r1-reduce-axioms.txt`，exit_code 124）。
注：守卫已新增 `footprint_bytes` 计量——同一作业 lean 子进程
RSS 3.63GB 而 physical footprint 仅 553MB，超额部分是文件映射页。

## 5. 守卫尝试记录

| 任务 | 守卫退出 | RSS 峰值 | 日志 |
|---|---|---|---|
| `lake env lean -j2 -M4096 R1N4Capacity.lean` | 124 (RSS_LIMIT, 25s) | 4.21 GiB | r1-reduce-build.txt |
| 探针 `r1-reduce-axioms.lean` | 124 (RSS_LIMIT, 3.7s) | 4.32 GiB | r1-reduce-axioms.txt |
| `import S7Defs` 单行探针 | 124 (8.4s) | 4.26 GiB | /tmp/r1_probe_tiny.log |
| 窄 import（Real.Basic+Linarith）探针 | 0 | 2.01 GiB | /tmp/r1_probe_min.log |
| 零 import 空文件 | 0 | 1.05 GiB | /tmp/r1_probe_nil.log |
