# Six weak-outer / double-low mask472 local verification — 2026-10-08

All seven originally SOURCE_ONLY candidates now have a successful local strict compilation and a genuine normal target build. Eleven selected declarations pass the standard-axiom gate. `SixWeakOuterReplay` contains definitions only and has no selected theorem prints; its empty selection is not represented as an axiom audit. Final successful runs produced zero owned source warnings.

## Verified scope

This is the single mask472 pilot (catalog index26), with fixed n4 and `0 <= delta < 1`:

- A: defect at row 1 <= 2 and defect at row 3 <= 3; 75 contexts, 65 unique literal cycles.
- B: defect at row 0 <= 2 and defect at row 2 <= 2; 225 contexts, 113 unique literal cycles.

No all62 data generation or typed all62 verification was performed or claimed. The ten-way dispatch in the original preparation state remains Python-only; this batch does not turn it into a Lean coverage theorem. No solver, generator, all62 dispatch, or full-project check was run under this lease.

## Local acceptance and resources

Root authorized one exclusive compiler slot. Every check used the existing process-tree guard: 8 GiB RSS, 180 seconds, and a global maximum of one Lean process. Strict checks used `--trust=0 -M8192 -DautoImplicit=false`. Each genuine normal pass required an actual `Built` message for that module, successful build completion, the same source bytes as its strict pass, and its selected standard-axiom reports. Owned dependencies had to pass genuine normal compilation on their current bytes before dependent checks could start.

All successful selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No resource stop occurred in any attempt. Peak tree RSS including failed attempts was 5,695,472 KiB; the longest individual attempt was 61.801 seconds.

| Module | Successful strict / normal attempt | Strict / normal seconds | Selected declarations |
| --- | --- | --- | --- |
| `SixWeakOuterReplay` | 1 / 1 | 5.207 / 3.413 | 0 |
| `SixWeakOuterFloorProfiles` | 1 / 1 | 45.767 / 52.125 | 2 |
| `SixWeakOuterReplaySoundness` | 2 / 1 | 49.420 / 61.801 | 5 |
| `SixWeakOuterMask472Data` | 2 / 1 | 4.575 / 5.096 | 1 |
| `SixDoubleLowMask472Data` | 2 / 1 | 7.057 / 10.650 | 1 |
| `SixWeakOuterMask472` | 1 / 1 | 54.746 / 42.139 | 1 |
| `SixDoubleLowMask472` | 1 / 1 | 49.783 / 54.575 | 1 |

Each module's subdirectory contains its complete `checkpoint.json`, exact input snapshots, and full raw outputs for every attempt. `final-result.json` cross-checks current source hashes, all snapshots/raw hashes, genuine build confirmations, selected axiom reports, warnings, and failed attempts.

## Preserved failures and API-only repairs

Three first strict candidates failed and were preserved byte-for-byte with their raw outputs:

- ReplaySoundness original `e9a452d0...`: `edgeHolds` was out of scope. One repair opened the already imported `N4R2CriticalCycleSoundness` namespace and removed one diagnosed unused old-decoder simp argument.
- Weak472Data original `f36e0c7b...`: `Library` was ambiguous between two existing aliases. One repair qualified the type as `SixWeakOuterReplay.Library`.
- Double472Data original `79776ba8...`: the same alias ambiguity; the same one-line qualification repaired it.

Each repaired module passed strict attempt02 and genuine normal attempt01. No theorem statement, A/B bound, literal cycle, origin, ID array, or mathematical premise was changed. The other four candidate sources stayed byte-for-byte unchanged. Original initial hashes, final approved hashes, repair reasons, and failing snapshot/raw paths remain in `manifest.json`; the original preparation state was not rewritten. The failed compilation outputs contain temporary `sorryAx` dependencies caused by their errors and are explicitly NOT_PROVED; none is treated as an acceptance result.

The old five checked exactword000 modules and Catalog663 stayed unchanged under before/after source-hash checks. The original generator stayed unchanged and was not run. The exporter still emits the unqualified `Library` type at line 38. Any future authorized export needs to retain the checked data type qualification; the now-checked shared soundness helper must also stay frozen.

## Final frozen candidate sources

| Module | SHA256 |
| --- | --- |
| `SixWeakOuterReplay` | `24a46b6c03628bc6e03cc551bd870723e96ce56ef7deba38af05d0357e6cf0d4` |
| `SixWeakOuterFloorProfiles` | `7e6c1544d72a6f56524c5803f9fb15298400617e01766345adad6bf1ea4e1e64` |
| `SixWeakOuterReplaySoundness` | `9dc39a8a10e9e15b2437290c96f7550c196ce13aa8fbef1dda8f09920afe1872` |
| `SixWeakOuterMask472Data` | `f701c3db15fe1ac0c49037965af98977c109d1b6b55b84e8dcd037a13f9ea18a` |
| `SixDoubleLowMask472Data` | `f2b9c6edd15eca8b3a59c4f8137d34e0c52c6400cea34c6bb879d6790eea22c1` |
| `SixWeakOuterMask472` | `cf496328fe5a818f25516daa4f3e242d5d89184eddf209d6a3b77f4f32b7fcba` |
| `SixDoubleLowMask472` | `e7995435f534cdbaea58b7a339114c1da33ea3fb1febc3d2720f660070c3b6b3` |

## Eleven selected declarations

- `Jsp404.SixWeakOuterFloorProfiles.positive_cell`
- `Jsp404.SixWeakOuterFloorProfiles.weak_two_profile`
- `Jsp404.SixWeakOuterReplaySoundness.decode_sound`
- `Jsp404.SixWeakOuterReplaySoundness.cycleCheck_sound`
- `Jsp404.SixWeakOuterReplaySoundness.libraryCheck_sound`
- `Jsp404.SixWeakOuterReplaySoundness.leafCheckA_sound`
- `Jsp404.SixWeakOuterReplaySoundness.leafCheckB_sound`
- `Jsp404.SixWeakOuterMask472Data.point_checked`
- `Jsp404.SixDoubleLowMask472Data.point_checked`
- `Jsp404.SixWeakOuterMask472.weak75_mask472_impossible`
- `Jsp404.SixDoubleLowMask472.double225_mask472_impossible`

The exclusive slot was formally returned to Root immediately after the final Double472 normal process exited. All own Lean/Lake processes had exited; no subsequent target was started.
