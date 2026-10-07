# Outer-left replay: checked actual soundness core

Status: **SCOPED_PASS_N4_R2_OUTER_LEFT_REPLAY_SOUNDNESS**. The first
strict `--trust=0` check and first genuine normal build both exited zero
on the unchanged source. All nine selected exports have exactly the
standard three axioms. This is finite leaf-certificate soundness; a
complete terminal exclusion is not claimed by this module alone.

Source: `Jsp000404/N4R2OuterLeftReplaySoundness.lean`, 231 lines, nine
selected public exports. SHA-256:
`e69febc9ecd62dbcef3f5b291b26fd7e0439b150ecf7e78c9fe46c42f0b80630`.

## Actual roles and exact scope

The model is the unchanged `SatScalarModel.GenericModel 7 4`. Its
ordinary fields already include `0 ≤ delta < 1`, actual theta order,
corridors, triangle arms, and complete sorted row multisets.

The new outer-left profile is deliberately distinct from the frozen
between profile:

- Row `1` has actual full-row defect `2` and supplies one internally
  chosen necessary weak28 lower profile.
- Rows `2..6`, expressed by `1 < i.val`, have actual full-row defect `4`
  and supply strict full-gap upper bounds of `2`.
- Row `0` has no prescribed defect. Only genuine model constraints and
  actual full-gap nonnegativity are used there.

There is no `HIGH` premise, no extra delta sign premise, and no
reinterpretation of the frozen low-center pair `0/6`.

## Implemented semantic chain

`checked_rows_perm_sorted` and `checked_fullGaps_eq_modelGap` reuse the
frozen literal-row soundness interface: all six off-center labels,
distinctness, and every comparison are checked against the actual word.
No row order, sorting oracle or accepted-checker field is added to the
model.

`lowerArcWithRows_sound` and `upperArcWithRows_sound` transport complete
literal rows through the frozen public `toArc`, `lowerArc_eq` and
`upperArc_eq` bridges. Both linear endpoint gaps are retained. The lower
helper allows zero; the upper helper requires the actual row's defect
to equal four.

`lowLowerValue_sound` interprets the new profile selector at actual
center `1`. A missing profile or zero profile entry gives only the
actual nonnegative lower bound. All other centers use that same genuine
zero lower bound.

`decode_sound` handles each new pure origin. Common theta, corridor and
triangle edges are interpreted directly from the actual model. It does
not invoke the frozen old-role decoder with fabricated tail or low-row
premises. New gap-upper origins are sound only after the decoder's
`1 < i.val` test identifies an actual tail center.

`cycleCheck_sound` converts the finite path and exact integer weights
to the frozen shared cycle checker and supplies every real edge from
`decode_sound`. `libraryCheck_sound` checks the actual lookup.
`leafCheck_sound` validates the row header, then interprets either the
tail certificate or all 28 necessary low1 profiles. In the low branch
the actual complete row internally supplies its profile witness via
`exists_low_profile M 1 hdef1`.

The Boolean checks in these helper statements are finite certificate
premises. They are not capacity, feasibility, solver, or accepted-row
premises about the actual model. A caller-free terminal must obtain
the concrete checks from a separately checked exhaustive data module.

## Coverage boundary

Uniform explicitly confirmed that words `68`, `1390`, `4537`, and
`17900` are representative pilot samples. They are **not** a four-word
residual list or exhaustive cover of tail-compatible actual models.
The 112 pilot word/profile checks and an external solver's global
UNSAT result are not used as a Lean theorem or as a coverage premise.

The planned complete terminal requires the new
`N4R2OuterLeftAllChecked` API for all 24698 catalog entries. The frozen
`N4R2ModelCatalog.exists_catalog_model_word M` can then choose the actual
word and its catalog index internally. Until that exhaustive new data
bridge is available and checked, this module supplies only no-data
soundness; it does not assert `outer_left_low1_pure_tail_impossible`.

## Ownership and dependencies

Uniform owns the new pure decoder, generator and finite data. This task
owns only the new actual soundness file and this note. No frozen
between, old PASS source, pure decoder or data file was edited.

The checked pure API read here was
`N4R2OuterLeftReplay.lean`, 74 lines, SHA-256
`e7fb147aff845d19aa82885f901ff20dedc86de558a1ba5624534e9d4b31bc38`.
The frozen literal-row, thin replay, reified arc and shared cycle APIs
were inspected directly. Independent integration review found no
concrete math/API blocker in the row-order substitution, profile alias,
new center roles, cycle-field transport or profile selection. This was
read-only static review, not a compile result. Uniform also reviewed the
new role and pure-definition consumption without identifying a mismatch.
No Git operation or old PASS source modification was performed.

## Verification and immediate release

- Strict attempt 01: actual exit 0, 9.67595 seconds, sampled peak process
  tree RSS 3,740,992 KiB; nine standard-three-axiom results, zero own
  warnings.
- Genuine normal attempt 01: actual exit 0, 6.75821 seconds, sampled peak
  process tree RSS 3,790,288 KiB; the own module was genuinely built and
  the build completed successfully (3286 jobs). All nine selected axiom
  results were printed again. Own and inherited warnings are separately
  recorded in the receipt.
- Source unchanged; no failed attempts, resource stops or API repairs.
- Actual guard was single 8 GiB / 180 seconds, globally at most one Lean
  process. The initial 8 GiB choice used the known 3.72–3.80 GB process-tree
  peaks of the frozen related soundness modules. No 3 GiB run was made or
  represented as a failure. The actual new strict peak also exceeded 3 GiB.
- Both processes exited before immediate formal release to root for the
  next queued geometry modules. No batch authorization was forwarded and
  no further Lean invocation occurred during receipt preparation.

All exact source snapshots, complete raw outputs, driver and checkpoint
are preserved in `verification/oct7-n4-r2-outer-left-replay-soundness/`.
The receipt is
`research/JSP404_N4_R2_OUTER_LEFT_REPLAY_SOUNDNESS_RECEIPT_20261007.json`.
