# Verification receipt: DevinF17HullGap (2026-10-07/08 UTC)

Partial, scoped result. The original arbitrary-N theorem remains OPEN;
`MainTheorem` lower N>=17 still depends on `sorryAx`. Nothing here claims completion.

- Repository base: `bd120994b033f7e8e92ff779b795d00db305110c`
  (owner branch review/jsp404-proof-continuation-20261004, untouched)
- Branch: `agent/devin-f17-hull-gap-20261008`
- Toolchain: `leanprover/lean4:v4.34.0`; mathlib `5ed2965256430c3649e86755f9576b54eca72435` (see environment.txt)
- Machine: Devin cloud VM, 8 vCPU, Linux x86_64 (not the user's Mac)
- New source: `Jsp000404/DevinF17HullGap.lean`
- Final source SHA-256: `3b02d377d28a025e82eb574055b143bf3da7acfa0a1956b9b0b731817314b615` (also source.sha256; byte copy DevinF17HullGap.final.lean)

## Runs (final source only)

| step | command | exit | wall | log |
|---|---|---|---|---|
| strict check | `lake env lean --trust=0 Jsp000404/DevinF17HullGap.lean` | 0 | 4.86 s | trust0.log, trust0.time, trust0.meta |
| genuine build | `lake build Jsp000404.DevinF17HullGap` | 0 | 8.33 s | build.log, build.time, build.meta |
| axiom check | `lake env lean --trust=0 verification/devin-f17-hull-gap-20261008/AxiomCheck.lean` | 0 | ~4 s | axiom_check.log |

- Build evidence: `.lake/build/lib/lean/Jsp000404/DevinF17HullGap.olean` did not exist
  before the build (prebuild_state.txt) and was produced at 2026-10-07 19:01:16 UTC
  (postbuild_state.txt, olean sha256 dc291ffcdb2e5c3e444582b96fff662265b3a6049f01ecc5b98a8ebb00ed5eff).
  build.log line: `[8997/8997] Built Jsp000404.DevinF17HullGap (4.6s)`. The target module was
  genuinely compiled; its 8996 dependencies were replayed from the earlier genuine dependency
  build (Build completed successfully (8996 jobs), ~5 min, same VM) and are NOT claimed as rebuilt here.
- Warnings in the new module: none (trust0.log contains only `#print axioms` output).
- Axioms of every exported declaration: `[propext, Classical.choice, Quot.sound]` only.
- Forbidden-token scan (sorry/admit/axiom/unsafe/native_decide/implemented_by/extern):
  no matches (forbidden_scan.txt).
- No existing file modified; failed iterations: FAILED_ITERATIONS.md.
