# Indexed cyclic row-gain bridge — SOURCE_ONLY

New source: `Jsp000404/RowGainCyclicIncident.lean`, 173 lines, SHA
`cca1b1762acee3bd56956a4ef0049d6f18465bd4be5df1585dc6e2b1aad3d397`.
It has not been compiled. The sole selected declaration is
`Jsp404.RowGainCyclicIncident.rowGain_eq_mergeGain_gapAfter`.

Its exact indexed claim is

```lean
theorem rowGain_eq_mergeGain_gapAfter {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.SortedLE) (hnd : l.Nodup)
    (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi) (h2 : 2 ≤ l.length)
    (K : Fin l.length) :
    rowGain lam l K.val = mergeGain lam
      (gapAfter l ((finRotate l.length).symm K)) (gapAfter l K)
```

The proof internally relates the actual rotated-erasure predecessor and
successor to the full original list. First, Nodup and length at least two
exclude the rotated wrapGap all-equal branch. The first, internal and
last positions then use the actual take/drop/head/getLast identities
already used in `Deletion.wrapGap_merge_sortedLE`. The predecessor is a
genuine permutation `finRotate.symm`, including last-to-first wrap.
No rotated list is assumed SortedLE. Equal numerical gap lengths remain
separate indexed occurrences; no Finset of distinct gap values is used.

The output consumes the checked `rowGain_eq_mergeGain` and produces the
indexed merge identity rather than assuming it. It supplies no deletion
budget, row score, actual point count or capacity conclusion. A separate
actual observer-degree consumer will construct its own unique direction
indices from actual legality and use this bridge after verification.

The selected-name file, actual dependency-source hashes, and prepared
8 GiB / 180 second / globally single Lean-or-Lake guard are recorded in
`verification/oct8-row-gain-cyclic-incident/SOURCE_READY.json`.
The runner refuses to launch if any Lean or Lake process already exists,
preserves exact source bytes and full raw output per attempt, and allows
at most three attempts per mode. It has not been launched; Root's formal
resource grant is required. The intended axiom check accepts only
`propext`, `Classical.choice` and `Quot.sound`, with no result claimed yet.

Only this new source, note and new preparation directory were written.
No Lean, solver, Git, quota operation, old PASS edit or change to the
verified Apex source was performed.
