# R2/N4 milestone audit — 2026-10-10

Tested code SHA: `3d0d5d8adaa4b080fba6d3f5a2ce917b02629cbc`
Branch: `agent/jsp404-air-emergency-owner-20260928`
Toolchain: `leanprover/lean4:v4.34.0`; mathlib `5ed2965256430c3649e86755f9576b54eca72435`
Status: **MODULE_VERIFIED / FULL_ROOT_BUILD PASS** — pushed `f629a89..3d0d5d8`.

## 1. Declaration semantics (read back via `#check`, exit 0)

| theorem | content verified |
|---|---|
| `r2_n4_overcap_reduces` | `t ≥ 6`, `⌊π/λ⌋ = 4`, `R2N4Profile`, `potential > 2^4+2^2` ⇒ literal sub-configuration `c' = c ∘ ι` with the seven-centre `(1,2,2,3,4,4,4)` profile **or** the eight-centre `(1,2,2,4,4,4,4,4)` profile. Defects stated on the original `directionRow o e c'` reference; legality preserved. |
| `seven_centre_n4_terminal` | `Fin 7` centres, `⌊π/λ⌋ = 4`, legality; anchor defect `1`, rows `a,b` defect `2`, row `u` defect `3`, all pairwise distinct ⇒ `False`. No model/MSig/emission/`CertExists` hypothesis. |
| `eight_centre_n4_terminal` | `Fin 8` centres, anchor defect `1`, rows `a,b` defect `2` ⇒ `False`. Tail defect-`4` rows inert. |
| `r2_n4_overcap_impossible` | Same hypotheses as the reducer ⇒ `False` directly. HIGH-band capacity cap `20 = 2^4 + 2^2`. |

No hidden premises: every hypothesis is a geometric/legality/defect
statement on the original configuration. The SMT trees appear only as
already-compiled kernel theorems below `s7cert_*`/`s8cert_*`.

## 2. Transitive axioms

`#print axioms` on the four head theorems and all 15 position-class
terminals: **`[propext, Classical.choice, Quot.sound]`**, no `sorryAx`,
no foreign axioms. Raw output: `verification/r2-n4-final-axioms.txt`.

## 3. Coverage

`tools/s7_leaf_trees_lin.json` (sha256 `b7a511e1…`), `1404 = 12×108 + 3×36`
top-level combinations:

- S7: 12 position families × `6 defect-2 sigs × 6 defect-2 sigs × 3 defect-3 sigs = 108`.
- S8: 3 families × `6 × 6 = 36`.

Dispatcher coverage is structural, not module-count: `S7Certs` /
`S8Certs` `rcases` over `msig{1,2}_{7,8}_canon_of_pos` produce a branch
for every canonical signature class; each branch calls its generated
leaf theorem. All 97 leaf modules + `S7LeavesTest` (an early smoke
sample leaf, kept — also kernel-checked) compile to `.olean`; the
heaviest single tree `s8_BT/H_I,H_I` (95,659 nodes) is replayed via
the emitted sub-theorem chunking.

Extraction → dispatch chain (all kernel):
`SatChart` → `n{7,8}σ` rank lemmas (`{0,1}`/`{4,5}`/`{0,5}` or `{0,6}`)
→ `n{7,8}_row{1,2}_exists` (row signature + `List.Perm` over scalar
model chords) → `s{7,8}cert_*` → 12/3 terminals →
`{seven,eight}_centre_n4_terminal` → `r2_n4_overcap_impossible`.

## 4. Root import

`Jsp000404.lean` now imports `R2N4Capacity`, `S7Extraction`,
`S8Extraction`, `S7Dispatch`, `S8Dispatch`, `R2N4Assembly`
(leaf modules arrive transitively through `S{7,8}Certs`).

## 5. Full root build

`nice -n 15 lake build` on the frozen SHA: **9146 jobs, exit 0**,
root `Jsp000404` built. Raw log: `verification/r2-n4-final-build.txt`.

## 6. Historical sorries (recorded once — none on this chain)

| location | declaration |
|---|---|
| `Deletion.lean:1563` | `exists_removable_vertex` (frozen crux) |
| `Deletion.lean:1573` | `exists_removable_hull_vertex` |
| `GeometricDeletion.lean:680` | tail-emission helper |
| `Section4Legality.lean:165` | staircase tail |
| `PentagonGadgetBridge.lean:41` | `opponent_pentagon_high_bound` (third-party WIP) |
| `MainTheorem.lean:20` | `sendov_lower`, N≥9 branch |

`#print axioms` proves none is reachable from the audited theorems
(a `sorryAx` would appear in the output). This is **not** a
repo-wide sorry-free claim.
