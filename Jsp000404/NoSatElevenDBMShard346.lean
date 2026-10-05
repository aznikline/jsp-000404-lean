import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_346 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr016c, htr019b, htr069c])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr017c, htr019b, htr079c])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
    linarith only [hlam, htr018c, htr019b, htr089c])
  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr016b, htr069a, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc679xy, htr016a, htr019a, htr167a, htr169c])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, htr017b, htr079a, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc789xy, htr017a, htr019a, htr178a, htr179c])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
    linarith only [hlam, htr018b, htr089a, htr189a])
  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc146yz, htr016a, htr019a, htr169c, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hc147yz, htr017a, htr019a, htr179c, htr479a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc167yz, htr017a, htr019a, htr179c, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc178yz, htr018a, htr019a, htr189c, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd14a, hd89b, htr146a, htr467a, htr678a, htr789a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hc124yz, htr146b, htr167a, htr246a, htr467a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hd14a, hd69b, htr147a, htr246a, htr247a, htr469a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a]
    ·
      linarith only [hlam, hd16a, hd79b, htr167a, htr478a, htr479a, htr678a]
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc146yz, htr167b, htr178a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr124a, htr246a, htr467a, htr679a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hd14a, hd79b, htr146a, htr246a, htr247a, htr479a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      linarith only [hlam, hd14a, hd79b, htr147a, htr478a, htr678a, htr679a]
    ·
      linarith only [hlam, hc124yz, htr147b, htr178a, htr247a, htr478a]

theorem shard_346 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    : False :=
  proof_shard_346 m htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr019b htr124a htr146a htr146b htr147a htr147b

#print axioms shard_346
end Jsp404.NoSatElevenDBMTerminal
