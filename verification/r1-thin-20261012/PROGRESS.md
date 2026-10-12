# R1-THIN-CAPACITY-AND-ZERO-02 (thin checkout, AIR 794b5cd)

- `Jsp404.ThinSixCapacity.actual_six_sat_capacity` (Jsp000404/ActualN4SixSaturatedCapacity.lean, sha256 9a74cf22…d6ad):
  actual Fin 6, Section4Legality, floor(pi/lam)=4, one SAT row, e≠0 ⇒ potential ≤ 20. Normal + --trust=0 EXIT 0; axioms propext/Classical.choice/Quot.sound.
- `Jsp404.ActualZeroDeletionRigidity.actual_seven_zero_delete_normal_form` (Jsp000404/ActualZeroDeletionRigidity.lean, sha256 8b0e7a3b…03e9):
  actual Fin 7 legal, floor 4, SAT v, zero-score z, potential 21 ⇒ deleted potential 20, all surviving rowGain 0, scores unchanged.
  Normal (retry 1 after guard PSS-read race) + --trust=0 EXIT 0; axioms standard 3. Necessary rigidity only, not a contradiction.
- One source edit (zero v0→v1): `PositiveRowCount.rowScore_le_restrict` does not exist at 794b5cd; replaced by existing deletion lemmas.
- ThirdParty JSP404.{Basic,BinaryEncoding,DirectionalCover} oleans were missing from the payload; built from unmodified pinned sources under the guard.
- Depends on untracked Root extra `ActualMinimumDeletionNormalForm.lean` (not committed here; hash in manifest.json).
- Not pushed; awaiting Codex review. JSP404 all-N and `sendov_lower` remain OPEN.
