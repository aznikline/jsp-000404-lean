import Jsp000404.Deletion
import JSP404.BinaryEncoding

/-!
# Empty-bin bounds for an anchored direction row

This is the local counting step of the interval-cover route. Repeated
directions or several directions in one bin consume only one coordinate.
The two end gaps are charged to empty prefix/suffix bins. Geometry must
still supply the interval and the separating edge colors.
-/

namespace Jsp404

noncomputable def linearGapScore (lam left right : ℝ) : List ℝ → ℕ
  | [] => gapScore lam (right - left)
  | x :: xs => gapScore lam (x - left) + linearGapScore lam x right xs

private lemma tail_score_add_occupied_le (lam right : ℝ) (m : ℕ)
    (bin : ℝ → ℕ) : ∀ (xs : List ℝ) (x : ℝ),
    (x :: xs).Pairwise (fun a b => bin a ≤ bin b) →
    (∀ a ∈ x :: xs, bin a < m) →
    (∀ a ∈ x :: xs, ∀ b ∈ x :: xs, bin a ≤ bin b →
      gapScore lam (b - a) ≤ bin b - bin a - 1) →
    (∀ a ∈ x :: xs, gapScore lam (right - a) ≤ m - bin a - 1) →
    linearGapScore lam x right xs + ((x :: xs).map bin).toFinset.card ≤ m - bin x := by
  classical
  intro xs
  induction xs with
  | nil =>
    intro x _ hb _ he
    have hbx := hb x (by simp)
    have hex := he x (by simp)
    simp only [linearGapScore, List.map_cons, List.map_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.insert_empty, Finset.card_singleton]
    omega
  | cons y ys ih =>
    intro x hmono hb hs he
    have hxy : bin x ≤ bin y := (List.pairwise_cons.mp hmono).1 y (by simp)
    have ht := ih y (List.pairwise_cons.mp hmono).2
      (fun a ha => hb a (by simp [ha]))
      (fun a ha b hbb hab => hs a (by simp [ha]) b (by simp [hbb]) hab)
      (fun a ha => he a (by simp [ha]))
    have hstep := hs x (by simp) y (by simp) hxy
    have hby := hb y (by simp)
    by_cases hsame : bin x = bin y
    · have hxmem : bin x ∈ ((y :: ys).map bin).toFinset := by simp [hsame]
      have hc : ((x :: y :: ys).map bin).toFinset.card =
          ((y :: ys).map bin).toFinset.card := by
        rw [List.map_cons, List.toFinset_cons, Finset.card_insert_of_mem hxmem]
      rw [linearGapScore, hc]
      omega
    · have hstrict : bin x < bin y := by omega
      have hxnot : bin x ∉ ((y :: ys).map bin).toFinset := by
        simp only [List.mem_toFinset, List.mem_map]
        rintro ⟨a, ha, heq⟩
        have hya : bin y ≤ bin a := by
          rcases List.mem_cons.mp ha with rfl | ha
          · exact le_rfl
          · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hmono).2).1 a ha
        omega
      have hc : ((x :: y :: ys).map bin).toFinset.card =
          ((y :: ys).map bin).toFinset.card + 1 := by
        rw [List.map_cons, List.toFinset_cons, Finset.card_insert_of_notMem hxnot]
      rw [linearGapScore, hc]
      omega

/-- Local gap counts fit in the unused coordinates of an ordered bin cover. -/
theorem linearGapScore_le_empty_bins (lam left right : ℝ) (m : ℕ)
    (bin : ℝ → ℕ) (xs : List ℝ)
    (hmono : xs.Pairwise (fun a b => bin a ≤ bin b))
    (hb : ∀ a ∈ xs, bin a < m)
    (hstart : ∀ a ∈ xs, gapScore lam (a - left) ≤ bin a)
    (hstep : ∀ a ∈ xs, ∀ b ∈ xs, bin a ≤ bin b →
      gapScore lam (b - a) ≤ bin b - bin a - 1)
    (hend : ∀ a ∈ xs, gapScore lam (right - a) ≤ m - bin a - 1)
    (hempty : xs = [] → gapScore lam (right - left) ≤ m) :
    linearGapScore lam left right xs ≤ m - (xs.map bin).toFinset.card := by
  cases xs with
  | nil => simpa [linearGapScore] using hempty rfl
  | cons x xs =>
    have ht := tail_score_add_occupied_le lam right m bin xs x hmono hb hstep hend
    have hs := hstart x (by simp)
    have hx := hb x (by simp)
    rw [linearGapScore]
    omega

lemma gapScore_le_of_lt_mul {lam z : ℝ} (hlam : 0 < lam) (k : ℕ)
    (hz : z < ((k : ℝ) + 2) * lam) : gapScore lam z ≤ k := by
  have hq : z / lam < ((k + 2 : ℕ) : ℝ) := by
    push_cast
    exact (div_lt_iff₀ hlam).mpr hz
  have hf : Nat.floor (z / lam) < k + 2 := (Nat.floor_lt' (by omega)).mpr hq
  unfold gapScore
  omega

/-- Cover bins may be closed at their ends; their width is strictly below
lambda, so the floor bounds remain valid even at exact grid boundaries. -/
theorem linearGapScore_le_empty_uniform_bins {lam width start left right : ℝ}
    {m : ℕ} (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hl : start - left ≤ lam)
    (hr : right - (start + (m : ℝ) * width) ≤ lam)
    (bin : ℝ → ℕ) (xs : List ℝ)
    (hmono : xs.Pairwise (fun a b => bin a ≤ bin b))
    (hb : ∀ a ∈ xs, bin a < m)
    (hpos : ∀ a ∈ xs,
      start + (bin a : ℝ) * width ≤ a ∧
      a ≤ start + ((bin a : ℝ) + 1) * width) :
    linearGapScore lam left right xs ≤ m - (xs.map bin).toFinset.card := by
  have hlam : 0 < lam := hw.trans hwidth
  apply linearGapScore_le_empty_bins lam left right m bin xs hmono hb
  · intro a ha
    apply gapScore_le_of_lt_mul hlam
    have hbound := (hpos a ha).2
    have hmult := mul_lt_mul_of_pos_left hwidth (show 0 < (bin a : ℝ) + 1 by positivity)
    nlinarith
  · intro a ha b hbb hab
    have hpa := (hpos a ha).1
    have hpb := (hpos b hbb).2
    by_cases heq : bin a = bin b
    · have hdiff : b - a < lam := by rw [← heq] at hpb; nlinarith
      have hf : Nat.floor ((b - a) / lam) = 0 := by
        rw [Nat.floor_eq_zero, div_lt_one hlam]
        exact hdiff
      simp [gapScore, hf, heq]
    · have hd : 0 < bin b - bin a := by omega
      have hcast : ((bin b - bin a : ℕ) : ℝ) = (bin b : ℝ) - bin a :=
        Nat.cast_sub hab
      have hm' := mul_lt_mul_of_pos_left hwidth
        (show 0 < (bin b : ℝ) - bin a + 1 by rw [← hcast]; positivity)
      have hf : Nat.floor ((b - a) / lam) < bin b - bin a + 1 := by
        rw [Nat.floor_lt' (by omega), div_lt_iff₀ hlam]
        push_cast
        rw [hcast]
        nlinarith
      unfold gapScore
      omega
  · intro a ha
    have hba := hb a ha
    have hpa := (hpos a ha).1
    have hcast : ((m - bin a : ℕ) : ℝ) = (m : ℝ) - bin a :=
      Nat.cast_sub hba.le
    have hdiff : 0 < (m : ℝ) - bin a := sub_pos.mpr (by exact_mod_cast hba)
    have hm' := mul_lt_mul_of_pos_left hwidth hdiff
    have hf : Nat.floor ((right - a) / lam) < m - bin a + 1 := by
      rw [Nat.floor_lt' (by omega), div_lt_iff₀ hlam]
      push_cast
      rw [hcast]
      nlinarith
    unfold gapScore
    omega
  · intro _
    apply gapScore_le_of_lt_mul hlam
    have hm' := mul_lt_mul_of_pos_left hwidth (show (0 : ℝ) < m by exact_mod_cast hm)
    nlinarith

/-- **Strict first-bin margin.**  If the first direction's gap charge is
at least one below its bin index (`gapScore (x − left) + 1 ≤ bin x`),
the packing bound gains one unit: `score + occupied + 1 ≤ m`, so the
row's defect strictly exceeds its bin occupancy.  This deficit — not
mere bin-skipping — is what the residual accounting must supply
geometrically.  NOTE: `left` is the row's own anchor ray `θ_i`
(`anchored_rowScore_eq_linear`), not the cover start `λ`. -/
theorem linearGapScore_add_one_le_empty_bins (lam left right : ℝ) (m : ℕ)
    (bin : ℝ → ℕ) (x : ℝ) (xs : List ℝ)
    (hmono : (x :: xs).Pairwise (fun a b => bin a ≤ bin b))
    (hb : ∀ a ∈ x :: xs, bin a < m)
    (hstart : gapScore lam (x - left) + 1 ≤ bin x)
    (hstep : ∀ a ∈ x :: xs, ∀ b ∈ x :: xs, bin a ≤ bin b →
      gapScore lam (b - a) ≤ bin b - bin a - 1)
    (hend : ∀ a ∈ x :: xs, gapScore lam (right - a) ≤ m - bin a - 1) :
    linearGapScore lam left right (x :: xs) +
      ((x :: xs).map bin).toFinset.card + 1 ≤ m := by
  have ht := tail_score_add_occupied_le lam right m bin xs x hmono hb
    hstep hend
  have hxb := hb x (by simp)
  rw [linearGapScore]
  omega

/-- Uniform-cover version of the strict first-bin margin. -/
theorem linearGapScore_add_one_le_empty_uniform_bins
    {lam width start left right : ℝ}
    {m : ℕ} (_hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hr : right - (start + (m : ℝ) * width) ≤ lam)
    (bin : ℝ → ℕ) (x : ℝ) (xs : List ℝ)
    (hmono : (x :: xs).Pairwise (fun a b => bin a ≤ bin b))
    (hb : ∀ a ∈ x :: xs, bin a < m)
    (hpos : ∀ a ∈ x :: xs,
      start + (bin a : ℝ) * width ≤ a ∧
        a ≤ start + ((bin a : ℝ) + 1) * width)
    (hfirst : gapScore lam (x - left) + 1 ≤ bin x) :
    linearGapScore lam left right (x :: xs) +
      ((x :: xs).map bin).toFinset.card + 1 ≤ m := by
  have hlam : 0 < lam := hw.trans hwidth
  apply linearGapScore_add_one_le_empty_bins lam left right m bin x xs
    hmono hb hfirst
  · intro a ha b hbb hab
    have hpa := (hpos a ha).1
    have hpb := (hpos b hbb).2
    by_cases heq : bin a = bin b
    · have hdiff : b - a < lam := by rw [← heq] at hpb; nlinarith
      have hf : Nat.floor ((b - a) / lam) = 0 := by
        rw [Nat.floor_eq_zero, div_lt_one hlam]
        exact hdiff
      simp [gapScore, hf, heq]
    · have hd : 0 < bin b - bin a := by omega
      have hcast : ((bin b - bin a : ℕ) : ℝ) = (bin b : ℝ) - bin a :=
        Nat.cast_sub hab
      have hm' := mul_lt_mul_of_pos_left hwidth
        (show 0 < (bin b : ℝ) - bin a + 1 by rw [← hcast]; positivity)
      have hf : Nat.floor ((b - a) / lam) < bin b - bin a + 1 := by
        rw [Nat.floor_lt' (by omega), div_lt_iff₀ hlam]
        push_cast
        rw [hcast]
        nlinarith
      unfold gapScore
      omega
  · intro a ha
    have hba := hb a ha
    have hpa := (hpos a ha).1
    have hcast : ((m - bin a : ℕ) : ℝ) = (m : ℝ) - bin a :=
      Nat.cast_sub hba.le
    have hdiff : 0 < (m : ℝ) - bin a := sub_pos.mpr (by exact_mod_cast hba)
    have hm' := mul_lt_mul_of_pos_left hwidth hdiff
    have hf : Nat.floor ((right - a) / lam) < m - bin a + 1 := by
      rw [Nat.floor_lt' (by omega), div_lt_iff₀ hlam]
      push_cast
      rw [hcast]
      nlinarith
    unfold gapScore
    omega

/-- Sufficient condition for a strict first margin: the first direction
lands in bin `b ≥ 1` while its true gap from the row origin `left`
stays below `(b+1)·λ`. -/
theorem gapScore_add_one_le_of_gap {lam left x : ℝ} (hlam : 0 < lam)
    {b : ℕ} (hb : 1 ≤ b) (hgap : x - left < ((b : ℝ) + 1) * lam) :
    gapScore lam (x - left) + 1 ≤ b := by
  have h := gapScore_le_of_lt_mul hlam (b - 1) (by
    have hcast : ((b - 1 : ℕ) : ℝ) + 2 = b + 1 := by
      rw [Nat.cast_sub hb]; push_cast; ring
    rw [hcast]
    exact hgap)
  omega

/-- Geometric sufficient condition via the cover position bound: with
`start = λ`, the first direction satisfies `first ≤ λ + (b+1)·w`, so the
strict margin follows from `θ_i = left > (b+1)·w − b·λ`. -/
theorem gapScore_add_one_le_of_cover {lam width left first : ℝ} {b : ℕ}
    (hlam : 0 < lam) (hb : 1 ≤ b)
    (hpos : first ≤ lam + ((b : ℝ) + 1) * width)
    (horigin : ((b : ℝ) + 1) * width - (b : ℝ) * lam < left) :
    gapScore lam (first - left) + 1 ≤ b := by
  apply gapScore_add_one_le_of_gap hlam hb
  linarith

noncomputable def uniformBin (start width : ℝ) (m : ℕ) (x : ℝ) : ℕ :=
  min (Nat.floor ((x - start) / width)) (m - 1)

lemma uniformBin_lt {start width : ℝ} {m : ℕ} (hm : 0 < m) (x : ℝ) :
    uniformBin start width m x < m := by
  have h := Nat.min_le_right (Nat.floor ((x - start) / width)) (m - 1)
  unfold uniformBin
  omega

lemma uniformBin_monotone {start width : ℝ} {m : ℕ} (hw : 0 < width) :
    Monotone (uniformBin start width m) := by
  intro x y hxy
  apply min_le_min _ le_rfl
  exact Nat.floor_mono ((div_le_div_iff_of_pos_right hw).mpr (by linarith))

lemma uniformBin_position {start width : ℝ} {m : ℕ} (hm : 0 < m)
    (hw : 0 < width) {x : ℝ} (hx : x ∈ Set.Icc start (start + m * width)) :
    start + (uniformBin start width m x : ℝ) * width ≤ x ∧
      x ≤ start + ((uniformBin start width m x : ℝ) + 1) * width := by
  have hq : 0 ≤ (x - start) / width := div_nonneg (by linarith [hx.1]) hw.le
  constructor
  · have hb : (uniformBin start width m x : ℝ) ≤
        (Nat.floor ((x - start) / width) : ℝ) := by
      exact_mod_cast Nat.min_le_left (Nat.floor ((x - start) / width)) (m - 1)
    have hmul := (le_div_iff₀ hw).mp (hb.trans (Nat.floor_le hq))
    linarith
  · by_cases hsmall : Nat.floor ((x - start) / width) ≤ m - 1
    · rw [uniformBin, min_eq_left hsmall]
      have hmul := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one ((x - start) / width))
      linarith
    · rw [uniformBin, min_eq_right (by omega)]
      have he : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ m by omega))
      rw [he]
      exact hx.2

/-- The index assignment is constructed from the interval, including its
right endpoint. Only the real sorted direction row is supplied. -/
theorem linearGapScore_le_empty_of_interval {lam width start left right : ℝ}
    {m : ℕ} (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hl : start - left ≤ lam)
    (hr : right - (start + m * width) ≤ lam)
    (xs : List ℝ) (hs : xs.SortedLE)
    (hx : ∀ x ∈ xs, x ∈ Set.Icc start (start + m * width)) :
    linearGapScore lam left right xs ≤
      m - (xs.map (uniformBin start width m)).toFinset.card := by
  apply linearGapScore_le_empty_uniform_bins hm hw hwidth hl hr
  · exact hs.pairwise.imp (fun h => uniformBin_monotone hw h)
  · exact fun x _ => uniformBin_lt hm x
  · exact fun x hmem => uniformBin_position hm hw (hx x hmem)

/-- Combine the local count with disjoint binary subcubes. The remaining
geometric task is to construct the bins and the separating bits. -/
theorem weighted_interval_packing {V : Type*} [Fintype V]
    (m : ℕ) (specified : V → Finset (Fin m)) (bit : V → Fin m → Bool)
    (ks : V → ℕ)
    (hseparate : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hlocal : ∀ v, ks v ≤ m - (specified v).card) :
    ∑ v, 2 ^ ks v ≤ 2 ^ m := by
  have hbound := JSP404.sum_free_binary_coordinates_le m specified bit hseparate
  exact le_trans (Finset.sum_le_sum (fun v _ =>
    Nat.pow_le_pow_right (by omega) (hlocal v))) hbound

/-- **End-bin obstruction (pure covering arithmetic).**  If `n` bins of
width `w` starting at `start` must reach `hi` (`hi ≤ start + n·w`) and
the corridor part above `t` exceeds what `n−1` bins can hold
(`hi − t > (n−1)·w`), then the first bin straddles `t`: no bin lies
entirely inside a bottom sliver `[·, t)`.  In the Sendov corridor
`hi − t = L − lB ≥ (n−1)λ > (n−1)·w` once `θ_m − θ_2 ≥ α`. -/
theorem first_bin_straddles {n : ℕ} {start w hi t : ℝ}
    (hhi : hi ≤ start + (n : ℝ) * w)
    (hwide : (n : ℝ) * w - w < hi - t) : t < start + w := by
  by_contra h
  push_neg at h
  linarith

/-- Dual for the top sliver: if the part below `t` exceeds `n−1` bins
(`t − lo > (n−1)·w`, with `lo` the corridor bottom) then the last bin
starts below `t` — no bin lies entirely inside `[t, ·)`. -/
theorem last_bin_straddles {n : ℕ} {start w lo t : ℝ}
    (hlo : start ≤ lo)
    (hwide : (n : ℝ) * w - w < t - lo) : start + (n : ℝ) * w - w < t := by
  by_contra h
  push_neg at h
  linarith

/-- **Sliver threshold inside the first bin.**  In the residual regime
`θ_m − θ₂ ≥ α = (n+1)λ − π` (the double-end consequence of
`potential_le_high_of_saturated_delete_span`), the full-corridor uniform
cover forces `θ₂ < width`: the bottom sliver `[λ+θ₁, λ+θ₂)` sits strictly
inside bin `0`, which therefore also contains middle-corridor directions.
Hence *no bin is sliver-exclusive* — the chord-level sliver exclusivity
cannot be lifted to bin-level exclusivity; any charging scheme must bill
sliver chords against a bin shared with ordinary chords.  The top sliver
is symmetric. -/
theorem sliver_threshold_lt_width {n : ℕ} {lam width θm θ2 : ℝ}
    (_hlam : 0 < lam) (hn3 : 3 ≤ n)
    (_hn : Nat.floor (Real.pi / lam) = n)
    (hwidth : width < lam)
    (hcover : Real.pi - 2 * lam + (Real.pi - n * lam) ≤ (n : ℝ) * width)
    (hθm : θm ≤ Real.pi - n * lam)
    (hres : ((n : ℝ) + 1) * lam - Real.pi ≤ θm - θ2) :
    θ2 < width := by
  have hhi : Real.pi - lam + θm ≤ lam + (n : ℝ) * width := by linarith
  have hwide : (n : ℝ) * width - width <
      (Real.pi - lam + θm) - (lam + θ2) := by
    have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [hres]
  have := first_bin_straddles (n := n) (start := lam) (w := width)
    (hi := Real.pi - lam + θm) (t := lam + θ2) hhi hwide
  linarith

/-- Sum of the raw per-gap floors `⌊g/λ⌋₊` along the gaps of a row,
including the two end gaps.  `gapScore` additionally subtracts `1`
per big gap; keeping the raw floors makes the defect bookkeeping
exact. -/
noncomputable def linearFloorSum (lam left right : ℝ) : List ℝ → ℕ
  | [] => ⌊(right - left) / lam⌋₊
  | x :: xs => ⌊(x - left) / lam⌋₊ + linearFloorSum lam x right xs

/-- Number of gaps whose length reaches `lam` (floor `≥ 1`). -/
noncomputable def linearBigCount (lam left right : ℝ) : List ℝ → ℕ
  | [] => min ⌊(right - left) / lam⌋₊ 1
  | x :: xs => min ⌊(x - left) / lam⌋₊ 1 + linearBigCount lam x right xs

/-- Pointwise identity `gapScore g + min ⌊g/λ⌋ 1 = ⌊g/λ⌋`. -/
private lemma gapScore_add_min_floor (lam g : ℝ) :
    gapScore lam g + min ⌊g / lam⌋₊ 1 = ⌊g / lam⌋₊ := by
  simp only [gapScore]; omega

/-- `score + bigCount = floorSum`, gap by gap. -/
theorem linearGapScore_add_bigCount (lam left right : ℝ) :
    ∀ xs : List ℝ,
    linearGapScore lam left right xs + linearBigCount lam left right xs =
      linearFloorSum lam left right xs := by
  intro xs
  induction xs generalizing left with
  | nil => exact gapScore_add_min_floor lam (right - left)
  | cons x xs ih =>
    have h := ih x
    have h2 := gapScore_add_min_floor lam (x - left)
    simp only [linearGapScore, linearBigCount, linearFloorSum]
    omega

/-- `⌊a⌋₊ + ⌊b⌋₊ ≤ ⌊a + b⌋₊` for nonnegative reals. -/
private lemma natFloor_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌊a⌋₊ + ⌊b⌋₊ ≤ ⌊a + b⌋₊ := by
  apply Nat.le_floor
  have h1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb
  push_cast
  linarith

/-- The floor sum never exceeds the floor of the total interval length:
each `⌊g/λ⌋·λ ≤ g` and the gaps telescope to `right - left`. -/
theorem linearFloorSum_le_floor (lam left right : ℝ) (hlam : 0 < lam) :
    ∀ xs : List ℝ, xs.Pairwise (· ≤ ·) →
    (∀ x ∈ xs, left ≤ x ∧ x ≤ right) →
    linearFloorSum lam left right xs ≤ ⌊(right - left) / lam⌋₊ := by
  intro xs
  induction xs generalizing left with
  | nil => intro _ _; exact le_rfl
  | cons x xs ih =>
    intro hp hmem
    have hlx : left ≤ x := (hmem x (by simp)).1
    have hxr : x ≤ right := (hmem x (by simp)).2
    have htl : ∀ y ∈ xs, x ≤ y := fun y hy =>
      (List.pairwise_cons.mp hp).1 y hy
    have hmem' : ∀ y ∈ xs, x ≤ y ∧ y ≤ right := fun y hy =>
      ⟨htl y hy, (hmem y (by simp [hy])).2⟩
    have hrest := ih x (List.pairwise_cons.mp hp).2 hmem'
    simp only [linearFloorSum]
    have hdiv : ⌊(x - left) / lam⌋₊ + ⌊(right - x) / lam⌋₊ ≤
        ⌊(right - left) / lam⌋₊ := by
      have h1 := natFloor_add_le (div_nonneg (sub_nonneg.mpr hlx) hlam.le)
        (div_nonneg (sub_nonneg.mpr hxr) hlam.le)
      have h2 : (x - left) / lam + (right - x) / lam =
          (right - left) / lam := by ring
      rwa [h2] at h1
    omega

/-- The last gap's `min`-indicator is bounded by the whole big count. -/
private lemma min_floor_last_le_linearBigCount (lam : ℝ) :
    ∀ (left right x : ℝ) (xs : List ℝ) (hne : x :: xs ≠ []),
    min ⌊(right - (x :: xs).getLast hne) / lam⌋₊ 1 ≤
      linearBigCount lam left right (x :: xs) := by
  intro left right x xs
  induction xs generalizing x left with
  | nil => intro _; simp [linearBigCount]
  | cons y ys ih =>
    intro hne
    have hlast : (x :: y :: ys).getLast hne = (y :: ys).getLast (by simp) := by
      simp [List.getLast_cons]
    rw [hlast, linearBigCount]
    exact le_trans (ih x y (by simp)) (Nat.le_add_left _ _)

/-- If a row's big-gap count is `≤ 1` while its last gap reaches `λ`,
then all earlier gap floors vanish: the floor sum equals the last
floor.  This is the "internal gaps are small" half of the defect-`2`
classification. -/
private lemma linearFloorSum_eq_last_of_bigCount_le_one (lam : ℝ) :
    ∀ (left right : ℝ) (xs : List ℝ) (hne : xs ≠ []),
    1 ≤ ⌊(right - xs.getLast hne) / lam⌋₊ →
    linearBigCount lam left right xs ≤ 1 →
    linearFloorSum lam left right xs =
      ⌊(right - xs.getLast hne) / lam⌋₊ := by
  intro left right xs
  induction xs generalizing left with
  | nil => intro hne; exact absurd rfl hne
  | cons x xs ih =>
    intro hne hlast hB
    cases xs with
    | nil =>
      simp only [linearFloorSum, linearBigCount] at hB ⊢
      have h1 : min ⌊(x - left) / lam⌋₊ 1 = 0 := by
        have h2 := hlast
        simp only [List.getLast_singleton] at h2
        omega
      have h3 : ⌊(x - left) / lam⌋₊ = 0 := by omega
      simp [h3, List.getLast_singleton]
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      have hlast' : (x :: y :: ys).getLast hne = (y :: ys).getLast hne' := by
        simp [List.getLast_cons]
      have hBtail : linearBigCount lam x right (y :: ys) ≤ 1 := by
        have hge := min_floor_last_le_linearBigCount lam x right y ys hne'
        rw [linearBigCount] at hB
        rw [hlast'] at hlast
        omega
      rw [hlast'] at hlast
      have hF := ih x hne' hlast hBtail
      have hfirst : ⌊(x - left) / lam⌋₊ = 0 := by
        rw [linearBigCount] at hB
        have hge := min_floor_last_le_linearBigCount lam x right y ys hne'
        omega
      have hexp : linearFloorSum lam left right (x :: y :: ys) =
          ⌊(x - left) / lam⌋₊ + linearFloorSum lam x right (y :: ys) := rfl
      rw [hexp, hfirst, zero_add, hF, ← hlast']

/-- **Defect-`2` end-gap span bound.**  If a nonempty sorted row in
`[left, right]` has score `n − 2` and *both* end gaps reach `λ`, then
those are the only two big gaps, their floors sum to `n`, and the
directions span at most `right - left - n·λ` (`= δλ` when
`right - left = π`).  Internal-gap-big Type-II rows and Type-I rows
are not constrained by this lemma — it applies exactly to rows whose
two big gaps sit at the ends. -/
theorem linearGapScore_span_le_of_big_ends (lam left right : ℝ)
    (hlam : 0 < lam) {xs : List ℝ} (hne : xs ≠ [])
    (hsort : xs.Pairwise (· ≤ ·))
    (hmem : ∀ x ∈ xs, left ≤ x ∧ x ≤ right)
    (hf : lam ≤ xs.head hne - left)
    (hl : lam ≤ right - xs.getLast hne)
    {n : ℕ} (hn : ⌊(right - left) / lam⌋₊ = n)
    (hscore : linearGapScore lam left right xs + 2 = n) :
    xs.getLast hne - xs.head hne ≤ right - left - n * lam := by
  obtain ⟨x, xt, rfl⟩ := List.ne_nil_iff_exists_cons.mp hne
  have hFB := linearGapScore_add_bigCount lam left right (x :: xt)
  have hF : linearFloorSum lam left right (x :: xt) ≤ n := by
    have := linearFloorSum_le_floor lam left right hlam (x :: xt) hsort hmem
    omega
  have hB : linearBigCount lam left right (x :: xt) ≤ 2 := by omega
  have hhead : (x :: xt).head hne = x := rfl
  have hff : 1 ≤ ⌊(x - left) / lam⌋₊ := by
    apply Nat.le_floor
    rw [hhead] at hf
    have h1 : (1 : ℝ) ≤ (x - left) / lam := by
      rw [le_div_iff₀ hlam]; linarith
    exact_mod_cast h1
  have hfl : 1 ≤ ⌊(right - (x :: xt).getLast hne) / lam⌋₊ := by
    apply Nat.le_floor
    have h1 : (1 : ℝ) ≤ (right - (x :: xt).getLast hne) / lam := by
      rw [le_div_iff₀ hlam]; linarith
    exact_mod_cast h1
  have hBtail : linearBigCount lam x right xt ≤ 1 := by
    rw [linearBigCount] at hB
    cases xt with
    | nil =>
      simp only [linearBigCount] at hB ⊢
      omega
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      have hge := min_floor_last_le_linearBigCount lam x right y ys hne'
      have hlast' : (x :: y :: ys).getLast hne = (y :: ys).getLast hne' := by
        simp [List.getLast_cons]
      rw [hlast'] at hfl
      omega
  have hBtail_ge : 1 ≤ linearBigCount lam x right xt := by
    cases xt with
    | nil =>
      simp only [linearBigCount]
      have hx : (x :: ([] : List ℝ)).getLast hne = x := by simp
      rw [hx] at hfl
      omega
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      have hlast' : (x :: y :: ys).getLast hne = (y :: ys).getLast hne' := by
        simp [List.getLast_cons]
      have h1 : min ⌊(right - (x :: y :: ys).getLast hne) / lam⌋₊ 1 = 1 := by
        omega
      have h2 := min_floor_last_le_linearBigCount lam x right y ys hne'
      rw [← hlast'] at h2
      omega
  have hFeq : linearFloorSum lam left right (x :: xt) =
      ⌊(x - left) / lam⌋₊ + ⌊(right - (x :: xt).getLast hne) / lam⌋₊ := by
    cases xt with
    | nil => simp [linearFloorSum, List.getLast_singleton]
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      have hlast' : (x :: y :: ys).getLast hne = (y :: ys).getLast hne' := by
        simp [List.getLast_cons]
      rw [hlast'] at hfl
      have htl := linearFloorSum_eq_last_of_bigCount_le_one lam x right
        (y :: ys) hne' hfl hBtail
      have hexp : linearFloorSum lam left right (x :: y :: ys) =
          ⌊(x - left) / lam⌋₊ + linearFloorSum lam x right (y :: ys) := rfl
      rw [hexp, htl, ← hlast']
  have hgle : (x :: xt).getLast hne ≤ right :=
    (hmem _ (List.getLast_mem hne)).2
  have hB' : linearBigCount lam left right (x :: xt) =
      min ⌊(x - left) / lam⌋₊ 1 + linearBigCount lam x right xt := rfl
  have hsum : ⌊(x - left) / lam⌋₊ + ⌊(right - (x :: xt).getLast hne) / lam⌋₊
      = n := by omega
  have hg1 : ⌊(x - left) / lam⌋₊ * lam ≤ x - left := by
    have h1 : (⌊(x - left) / lam⌋₊ : ℝ) ≤ (x - left) / lam :=
      Nat.floor_le (div_nonneg (by linarith [(hmem x (by simp)).1]) hlam.le)
    have h2 := mul_le_mul_of_nonneg_right h1 hlam.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlam)] at h2
  have hg2 : ⌊(right - (x :: xt).getLast hne) / lam⌋₊ * lam ≤
      right - (x :: xt).getLast hne := by
    have h1 : (⌊(right - (x :: xt).getLast hne) / lam⌋₊ : ℝ) ≤
        (right - (x :: xt).getLast hne) / lam :=
      Nat.floor_le (div_nonneg (by linarith [hgle]) hlam.le)
    have h2 := mul_le_mul_of_nonneg_right h1 hlam.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlam)] at h2
  have hheadx : (x :: xt).head hne = x := rfl
  rw [hheadx]
  have hcast : (⌊(x - left) / lam⌋₊ : ℝ) * lam +
      (⌊(right - (x :: xt).getLast hne) / lam⌋₊ : ℝ) * lam = n * lam := by
    have h3 : ((⌊(x - left) / lam⌋₊ +
        ⌊(right - (x :: xt).getLast hne) / lam⌋₊ : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hsum
    rw [Nat.cast_add] at h3
    have h4 := congrArg (· * lam) h3
    rw [add_mul] at h4
    exact h4
  nlinarith [hg1, hg2, hcast]

#print axioms linearGapScore_le_empty_uniform_bins
#print axioms linearGapScore_le_empty_of_interval
#print axioms weighted_interval_packing
#print axioms first_bin_straddles
#print axioms last_bin_straddles
#print axioms sliver_threshold_lt_width
#print axioms linearGapScore_add_one_le_empty_bins
#print axioms linearGapScore_add_one_le_empty_uniform_bins
#print axioms gapScore_add_one_le_of_gap
#print axioms gapScore_add_one_le_of_cover
#print axioms linearGapScore_add_bigCount
#print axioms linearFloorSum_le_floor
#print axioms linearGapScore_span_le_of_big_ends

end Jsp404
