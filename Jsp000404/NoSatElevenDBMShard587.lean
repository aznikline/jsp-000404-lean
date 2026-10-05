import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_587 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced029 := (m.htr 0 2 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr029a, htr029b, htr029c, _, _⟩
    linarith only [hlam, hc235xy, htr025a, htr029a, htr123a, htr129a])
  obtain ⟨htr029a, htr029b, htr029c, _, _⟩ := hforced029
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr026c, htr029b, htr069c])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr027c, htr029b, htr079c])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
    linarith only [hlam, htr028c, htr029b, htr089c])
  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, htr016b, htr069a, htr126b, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc679xy, htr012b, htr029a, htr126a, htr267a, htr269c])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, htr017b, htr079a, htr127b, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc789xy, htr012b, htr029a, htr127a, htr278a, htr279c])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
    linarith only [hlam, htr018b, htr089a, htr128b, htr289a])
  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc246yz, htr126a, htr129a, htr269c, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hc247yz, htr127a, htr129a, htr279c, htr479a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc267yz, htr127a, htr129a, htr279c, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc278yz, htr128a, htr129a, htr289c, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd24a, hd69b, htr247a, htr346a, htr347a, htr469a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
    ·
      linarith only [hlam, hd26a, hd79b, htr267a, htr478a, htr479a, htr678a]
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd24a, hd79b, htr246a, htr346a, htr347a, htr479a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      linarith only [hlam, hd24a, hd79b, htr247a, htr478a, htr678a, htr679a]
    ·
      linarith only [hlam, hc234yz, htr247b, htr278a, htr347a, htr478a]

theorem shard_587 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    : False :=
  proof_shard_587 m htr012b htr016b htr017b htr018b htr025a htr026c htr027c htr028c htr123a htr126a htr126b htr127a htr127b htr128a htr128b htr129a htr234a htr246a htr246b htr247a htr247b

#print axioms shard_587
end Jsp404.NoSatElevenDBMTerminal
