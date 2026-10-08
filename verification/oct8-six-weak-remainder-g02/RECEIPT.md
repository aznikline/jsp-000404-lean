# Group02 first-pass local acceptance — 2026-10-08

All five G02 targets passed first strict and genuine normal attempts on unchanged source bytes. All 114 public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. No compiler candidate failed; no source/API repair, owned warning, or resource stop occurred.

## Scope

G02 covers typed Catalog indices `[18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34]`, with masks `[216, 218, 222, 223, 254, 255, 448, 456, 504, 508, 510, 511, 512, 513, 515, 519]`. A uses only `GenericModel 5 4`, its selected typed `WordSound`, rowDefect 1 <= 2, and rowDefect 3 <= 3. B uses the corresponding typed word, rowDefect 0 <= 2, and rowDefect 2 <= 2. All actual row sorting, literal checker acceptance, and typed word bridges are constructed internally; no caller row, checker, profile, or coverage proof is added.

Together with old group00 and G01, 36 of 62 words are now checked. G03/G04 and the final catalog-cover/no-word A/B terminals remain SOURCE_ONLY. This receipt does not claim all 62 or actual R2 completion.

## Guarded checks

Root granted one exclusive compiler slot. The unchanged guards enforce one global Lean process, 8 GiB process-tree RSS, and 180 seconds per check. Strict mode used `--trust=0 -M8192 -DautoImplicit=false`. Genuine normal success required actual target `Built`, build completion, matching bytes, and complete selected-axiom reports. Owned dependencies had to have same-byte genuine normal passes before use.

| Target | Strict / normal seconds | Peak tree RSS across pair (KiB) | Public declarations |
| --- | --- | --- | --- |
| `SixWeakAllGroup02Data` | 35.898 / 32.751 | 2937312 | 16 |
| `SixDoubleAllGroup02Data` | 90.105 / 93.617 | 4095216 | 16 |
| `SixWeakAllGroup02Rows` | 95.259 / 94.927 | 4751776 | 48 |
| `SixWeakAllGroup02` | 62.617 / 86.585 | 4744864 | 17 |
| `SixDoubleAllGroup02` | 67.210 / 83.230 | 4229664 | 17 |

Every target passed attempt01 in each mode. Peak tree RSS was 4,751,776 KiB; the longest check was 95.259 seconds. No limit was extended. The 114 audited declarations comprise 16 A literal certificate checks, 16 B checks, 32 typed A/B catalog bridges, 16 actual row proofs, and 34 consumer results.

Full raw outputs, exact input snapshots, full commands, timings, RSS peaks, source/raw/artifact hashes, and all axiom reports remain in each target's `checkpoint.json`. `final-result.json` cross-checks every snapshot/raw hash, current source, genuine build confirmation, and the 114 public names. Since there were no failed compiler attempts, no failed candidate bytes are missing.

## Frozen sources

| Target | SHA256 |
| --- | --- |
| `SixWeakAllGroup02Data` | `f86950a1b83a3868ae2e38ef538b219f087891139a0106c9c0307cfa4527b9fc` |
| `SixDoubleAllGroup02Data` | `bec743b9446c42ccbf38e18ba26658ba1adb6cdeafc45511d18ea3d7acbfff9e` |
| `SixWeakAllGroup02Rows` | `eddd7148980ebe3c789420444a87a023228e8c6848d9e2131d6d2f9018fb5a20` |
| `SixWeakAllGroup02` | `18bb0d4281b0f6c825ed68a8a6a113f35cf82137e6b0f32a5de0fd36ae349e65` |
| `SixDoubleAllGroup02` | `59b42827226f8443741753f7b0e85b7ef538e1cc7212a17f47415da482c59cc6` |

All earlier PASS sources, Catalog663, Soundness9dc, and earlier exporters remained unchanged under before/after guards. No Root/Audit/old PASS source was edited. The original generation/cold-replay records remain separate historical static evidence, never substitutes for these kernel checks.

## Deferred work

G03 and G04 have been generated and independently cold-replayed, but were not compiled under this lease. The exact 62-index coverage source and no-word A/B sources also remain uncompiled. Their guards require actual same-byte genuine normal passes of all external group dependencies. No further target was started after this batch.

The exclusive slot was formally returned to Root immediately after the final B normal process exited; all own Lean/Lake processes had exited. The final all 62 scope will require fresh grants and successful checks of G03/G04 plus Cover/Complete A/B.
