# First 16 remainder group01: independent local acceptance, 2026-10-08

All five group01 targets passed first-attempt strict compilation and genuine normal target builds. Every one of the 114 public theorem prints uses only `propext`, `Classical.choice`, and `Quot.sound`. There were no failed compiler candidates, source/API repairs, owned warnings, or guard stops. All five generated sources remain unchanged from preparation.

## Exact verified scope

The checked catalog indices are 1 through 16, with masks `[1, 3, 7, 11, 15, 31, 63, 64, 72, 74, 75, 79, 95, 127, 192, 200]`. The two families have the exact intended bounds:

- A: `GenericModel 5 4`, rowDefect at row 1 <= 2 and row 3 <= 3.
- B: `GenericModel 5 4`, rowDefect at row 0 <= 2 and row 2 <= 2.

The individual and group consumers still take the actual typed `WordSound` for this 16-word group. They internally consume literal kernel-checked cycles/IDs, actual rows proved from triangle arms and symmetry, and typed word-to-Catalog bridges. No caller row order, profile, checker, or coverage premise was added. Other rows remain unrestricted.

Together with checked group00's four words, this is 20 of 62 catalog words. The remaining 42 words were not generated or checked under this lease. The complete kernel catalog coverage proof and final no-word A/B statements remain design-only. No all 62 or actual R2 completion is claimed here.

## Guarded local results

The Root-authorized exclusive slot used one global Lean process, 8 GiB process-tree RSS, and 180 seconds per check. Strict checks used `--trust=0 -M8192 -DautoImplicit=false`. Genuine normal acceptance required an actual target `Built` message, successful build completion, matching source bytes, and complete selected-axiom reports. Every owned dependency had to pass genuine normal compilation on its current bytes before consumption.

| Target | Strict / normal seconds | Peak tree RSS across pair (KiB) | Public declarations |
| --- | --- | --- | --- |
| `SixWeakAllGroup01Data` | 33.969 / 32.628 | 2900896 | 16 |
| `SixDoubleAllGroup01Data` | 86.405 / 89.587 | 3930528 | 16 |
| `SixWeakAllGroup01Rows` | 86.636 / 93.384 | 5089664 | 48 |
| `SixWeakAllGroup01` | 56.287 / 64.160 | 5011664 | 17 |
| `SixDoubleAllGroup01` | 40.296 / 61.825 | 5266368 | 17 |

Each target passed strict attempt01 and normal attempt01. The maximum check time was 93.384 seconds, and peak tree RSS was 5,266,368 KiB. The original limits were not extended. The 16-word shared Rows target passed in 86.636/93.384 seconds, so no smaller split was needed.

Per-target `checkpoint.json` files retain exact source snapshots, full raw outputs, commands, source/raw/artifact hashes, timings, RSS peaks, and all axiom reports. `final-result.json` cross-checks all ten snapshots/raw outputs, current sources, genuine build confirmations, and the 114 declarations. The original SOURCE_ONLY generation manifest and non-kernel cold replay remain unchanged as historical inputs.

## Measured grouping effect

Data imports are restricted to pure `SixWeakOuterReplay`; Catalog and typed bridges are confined to shared Rows. The 16-word AData target used 33.969/32.628 seconds and about 2.9 million KiB. The 16-word BData target used 86.405/89.587 seconds and stayed below 3.94 million KiB. This measured layout avoids repeatedly loading Catalog for Data while retaining all 32 typed A/B bridges in the kernel-checked Rows module. It supports considering similarly bounded later groups under fresh authorization and the same guards; it is not acceptance evidence for any ungenerated word.

## Frozen new source hashes

| Target | SHA256 |
| --- | --- |
| `SixWeakAllGroup01Data` | `3bdcdd28cb9a908738b71117a4253df24c1bd2fd6af5c654204ec9ef7bed5ede` |
| `SixDoubleAllGroup01Data` | `71e6d0aab5780eb7f67de2c1df48385dd45f4647285b59258f9a61ae7ab0d555` |
| `SixWeakAllGroup01Rows` | `c398ae0714d0ba4bb26e21acceed4f92b80497978da13bd7dd7ab8987c03b2e4` |
| `SixWeakAllGroup01` | `ed4a08cec53b370fbbd000860a0db02e005a603d132664ff02ab5bcde9aa1842` |
| `SixDoubleAllGroup01` | `267d4f6b883c22ba19d221eccca27a421235f7723d543095d7432065653585e1` |

The prior four-word sources, seven old pilots, five exactword000 sources, Catalog663, Soundness9dc, and older exporters stayed byte-for-byte unchanged under before/after guards. The new remainder generator is independently snapshotted in this group's directory.

## Separate preparation evidence and remaining work

Bounded single-process discovery generated 4800 contexts, with 830 A and 2168 B unique cycle records, in 2.987 seconds at 54,116,352 bytes RSS under 512 MiB / 30 second guards. The independent cold formula/literal replay checked 2998 cycle records, 32295 context edges, every origin and ID, and 480 row-order pairs in 0.127 seconds at 22,069,248 bytes RSS. Those static reports were not used as a substitute for the successful kernel checks.

`final-closure-design.lean.txt` remains explicitly DESIGN ONLY. It describes an internal 62-index coverage theorem proved by finite cases, then obtains the model's word using checked `exists_catalog_model_word M` and dispatches to old group00 plus groups01/02/03/04. Its proposed no-word statements match `ActualN4R2Critical22Adapter.WeakAComplete` and `WeakBComplete`; groups02/03/04 and that final coverage proof are not yet implemented acceptance artifacts.

## 114 audited public declarations

- `Jsp404.SixWeakAllGroup01Data.Mask001.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask003.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask007.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask011.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask015.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask031.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask063.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask064.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask072.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask074.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask075.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask079.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask095.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask127.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask192.point_checked`
- `Jsp404.SixWeakAllGroup01Data.Mask200.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask001.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask003.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask007.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask011.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask015.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask031.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask063.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask064.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask072.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask074.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask075.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask079.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask095.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask127.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask192.point_checked`
- `Jsp404.SixDoubleAllGroup01Data.Mask200.point_checked`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask001`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask001`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask001`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask003`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask003`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask003`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask007`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask007`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask007`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask011`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask011`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask011`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask015`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask015`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask015`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask031`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask031`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask031`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask063`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask063`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask063`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask064`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask064`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask064`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask072`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask072`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask072`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask074`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask074`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask074`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask075`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask075`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask075`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask079`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask079`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask079`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask095`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask095`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask095`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask127`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask127`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask127`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask192`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask192`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask192`
- `Jsp404.SixWeakAllGroup01Rows.word_catalog_mask200`
- `Jsp404.SixWeakAllGroup01Rows.double_word_catalog_mask200`
- `Jsp404.SixWeakAllGroup01Rows.rows_actual_mask200`
- `Jsp404.SixWeakAllGroup01.mask001_impossible`
- `Jsp404.SixWeakAllGroup01.mask003_impossible`
- `Jsp404.SixWeakAllGroup01.mask007_impossible`
- `Jsp404.SixWeakAllGroup01.mask011_impossible`
- `Jsp404.SixWeakAllGroup01.mask015_impossible`
- `Jsp404.SixWeakAllGroup01.mask031_impossible`
- `Jsp404.SixWeakAllGroup01.mask063_impossible`
- `Jsp404.SixWeakAllGroup01.mask064_impossible`
- `Jsp404.SixWeakAllGroup01.mask072_impossible`
- `Jsp404.SixWeakAllGroup01.mask074_impossible`
- `Jsp404.SixWeakAllGroup01.mask075_impossible`
- `Jsp404.SixWeakAllGroup01.mask079_impossible`
- `Jsp404.SixWeakAllGroup01.mask095_impossible`
- `Jsp404.SixWeakAllGroup01.mask127_impossible`
- `Jsp404.SixWeakAllGroup01.mask192_impossible`
- `Jsp404.SixWeakAllGroup01.mask200_impossible`
- `Jsp404.SixWeakAllGroup01.group_impossible`
- `Jsp404.SixDoubleAllGroup01.mask001_impossible`
- `Jsp404.SixDoubleAllGroup01.mask003_impossible`
- `Jsp404.SixDoubleAllGroup01.mask007_impossible`
- `Jsp404.SixDoubleAllGroup01.mask011_impossible`
- `Jsp404.SixDoubleAllGroup01.mask015_impossible`
- `Jsp404.SixDoubleAllGroup01.mask031_impossible`
- `Jsp404.SixDoubleAllGroup01.mask063_impossible`
- `Jsp404.SixDoubleAllGroup01.mask064_impossible`
- `Jsp404.SixDoubleAllGroup01.mask072_impossible`
- `Jsp404.SixDoubleAllGroup01.mask074_impossible`
- `Jsp404.SixDoubleAllGroup01.mask075_impossible`
- `Jsp404.SixDoubleAllGroup01.mask079_impossible`
- `Jsp404.SixDoubleAllGroup01.mask095_impossible`
- `Jsp404.SixDoubleAllGroup01.mask127_impossible`
- `Jsp404.SixDoubleAllGroup01.mask192_impossible`
- `Jsp404.SixDoubleAllGroup01.mask200_impossible`
- `Jsp404.SixDoubleAllGroup01.group_impossible`

The exclusive compiler slot was formally returned to Root immediately after the final B normal process exited. All own Lean/Lake processes had exited. No remaining 42, all 62, or full-project target was started under this lease.
