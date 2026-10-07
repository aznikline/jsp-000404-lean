# Four-mask SixWeak/SixDouble group local verification — 2026-10-08

All five group00 targets passed first-attempt local strict compilation and genuine normal target builds. All thirty public theorem prints use only `propext`, `Classical.choice`, and `Quot.sound`. There were no failed compiler candidates, source repairs, owned warnings, or resource stops. Every generated source remains byte-for-byte unchanged from preparation.

## Exact scope

The verified typed catalog indices are `[0,17,26,61]`, corresponding to masks `[000,202,472,1023]`. Both families are checked:

- A: any `GenericModel 5 4` with rowDefect at row 1 <= 2 and row 3 <= 3, under its selected four-word `WordSound`.
- B: any `GenericModel 5 4` with rowDefect at row 0 <= 2 and row 2 <= 2, under its selected four-word `WordSound`.

Each group consumer dispatches its four typed catalog indices internally. The four actual punctured-row orders are proved from the model's actual triangle arms and symmetry, then shared between A and B. Every finite certificate `point_checked` and every literal-word-to-typed-catalog equality has been checked by the Lean kernel. No caller row order, accepted cycle, profile certificate, or additional model premise was added.

This is four of 62 catalog words. The remaining 58 words, all 62 dispatch, and the final no-word `WeakAComplete`/`WeakBComplete` terminals are not generated or proved by this batch. The bounded Python generation and independent replay remain separately labeled static evidence; they are not substituted for these kernel checks.

## Guarded local acceptance

The Root-authorized exclusive compiler slot enforced one global Lean process, 8 GiB process-tree RSS, and 180 seconds per check. Strict checks used `--trust=0 -M8192 -DautoImplicit=false`. Each genuine normal pass required an actual target `Built` message, successful build completion, matching source hashes, and the same complete selected-axiom reports. Owned dependencies had to have genuine normal passes on their current bytes before consumption.

| Target | Strict / normal seconds | Peak tree RSS across pair (KiB) | Public declarations |
| --- | --- | --- | --- |
| `SixWeakAllGroup00Data` | 72.709 / 78.666 | 4842672 | 8 |
| `SixDoubleAllGroup00Data` | 72.133 / 80.766 | 5327680 | 8 |
| `SixWeakAllGroup00Rows` | 70.681 / 68.844 | 4925600 | 4 |
| `SixWeakAllGroup00` | 45.276 / 64.018 | 5164224 | 5 |
| `SixDoubleAllGroup00` | 56.503 / 64.364 | 4728928 | 5 |

Every target passed strict attempt01 and normal attempt01. The maximum check time was 80.766 seconds; peak tree RSS was 5,327,680 KiB. The limits were never extended. All ten exact source snapshots, raw outputs, full commands, resource measurements, and artifact hashes are retained in the per-target `checkpoint.json` files. `final-result.json` cross-checks all current source/raw/snapshot hashes and the thirty selected declarations.

The seven previously checked pilot sources, old five exactword000 sources, Catalog663, Soundness9dc, and the old exporter remained unchanged under before/after hash guards. The new generator's initial bytes are also saved independently as `generator-initial.source.py`.

## Generation and static evidence

`manifest.json` retains the original SOURCE_ONLY generation record. Discovery covered 1200 A/B contexts and 695 unique cycle records in 0.739 seconds at 37,289,984 bytes RSS. The separately implemented formula/literal replay checked 7983 context edges and all emitted vector/ID data in 0.040 seconds at 19,644,416 bytes RSS. Its source and raw output are preserved; the report remains explicitly non-kernel evidence.

The regenerated mask472 standalone units are byte-for-byte identical to the previous checked `f701c3db...` and `f2b9c6ed...` files before namespace grouping and typed-catalog witness insertion. The actual grouped witnesses, row proofs, and consumers are now independently kernel-checked as reported above.

## Frozen new source hashes

| Target | SHA256 |
| --- | --- |
| `SixWeakAllGroup00Data` | `21db948d7bec9d3b0bcfd0295517cb04cc875e7e7910563fad385cf7a498bd01` |
| `SixDoubleAllGroup00Data` | `540be0b62dbeca63841aef9131b85676f6653a0fb4001ab044c77cdaacf49e3c` |
| `SixWeakAllGroup00Rows` | `348453f5cf16d98aa4526cd51d381a4866829089a2238354b6819722b6b97420` |
| `SixWeakAllGroup00` | `7d6f42855ae1f49ad03e6d6e64539a34e2303ba709e8286b864c350a2b35b533` |
| `SixDoubleAllGroup00` | `6ea2e0ea4e4afafb4c01ea39c40ae8bff32f4cf357ce685529eebea97f75be38` |

## Follow-up efficiency assessment, not execution

A future separately authorized remainder generator can keep Data imports limited to pure Replay, moving literal-word-to-typed-Catalog equalities into shared row/bridge modules. That retains complete kernel correspondence while avoiding Catalog's import cost for Data checks. Data groups 16/16/16/10 are a candidate to measure under the same limits. Rows proof grouping needs its own bounded measurement: current four-row proof target took 70.681 seconds strict, while a consumer importing the completed Rows took 45.276 seconds, so cloning 58 row proofs into one target cannot be assumed to fit 180 seconds. No remaining-word generation or extra Lean target was started here.

## Thirty audited public declarations

- `Jsp404.SixWeakAllGroup00Data.Mask000.point_checked`
- `Jsp404.SixWeakAllGroup00Data.Mask000.word_catalog`
- `Jsp404.SixWeakAllGroup00Data.Mask202.point_checked`
- `Jsp404.SixWeakAllGroup00Data.Mask202.word_catalog`
- `Jsp404.SixWeakAllGroup00Data.Mask472.point_checked`
- `Jsp404.SixWeakAllGroup00Data.Mask472.word_catalog`
- `Jsp404.SixWeakAllGroup00Data.Mask1023.point_checked`
- `Jsp404.SixWeakAllGroup00Data.Mask1023.word_catalog`
- `Jsp404.SixDoubleAllGroup00Data.Mask000.point_checked`
- `Jsp404.SixDoubleAllGroup00Data.Mask000.word_catalog`
- `Jsp404.SixDoubleAllGroup00Data.Mask202.point_checked`
- `Jsp404.SixDoubleAllGroup00Data.Mask202.word_catalog`
- `Jsp404.SixDoubleAllGroup00Data.Mask472.point_checked`
- `Jsp404.SixDoubleAllGroup00Data.Mask472.word_catalog`
- `Jsp404.SixDoubleAllGroup00Data.Mask1023.point_checked`
- `Jsp404.SixDoubleAllGroup00Data.Mask1023.word_catalog`
- `Jsp404.SixWeakAllGroup00Rows.rows_actual_mask000`
- `Jsp404.SixWeakAllGroup00Rows.rows_actual_mask202`
- `Jsp404.SixWeakAllGroup00Rows.rows_actual_mask472`
- `Jsp404.SixWeakAllGroup00Rows.rows_actual_mask1023`
- `Jsp404.SixWeakAllGroup00.mask000_impossible`
- `Jsp404.SixWeakAllGroup00.mask202_impossible`
- `Jsp404.SixWeakAllGroup00.mask472_impossible`
- `Jsp404.SixWeakAllGroup00.mask1023_impossible`
- `Jsp404.SixWeakAllGroup00.group_impossible`
- `Jsp404.SixDoubleAllGroup00.mask000_impossible`
- `Jsp404.SixDoubleAllGroup00.mask202_impossible`
- `Jsp404.SixDoubleAllGroup00.mask472_impossible`
- `Jsp404.SixDoubleAllGroup00.mask1023_impossible`
- `Jsp404.SixDoubleAllGroup00.group_impossible`

The compiler slot was formally returned to Root immediately after the final B normal process exited. All own Lean/Lake processes had exited. No remainder 58, all 62, or full-project check was started under this lease.
