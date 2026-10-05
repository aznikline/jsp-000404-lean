import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_354 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr014c, htr019b, htr049c])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr015c, htr019b, htr059c])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr016c, htr019b, htr069c])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr017c, htr019b, htr079c])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr014b, htr049a, htr149a])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc459xy, htr014a, htr019a, htr145a, htr149c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc469xy, htr014a, htr019a, htr146a, htr149c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr015b, htr059a, htr159a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc569xy, htr015a, htr019a, htr156a, htr159c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
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
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc145yz, htr015a, htr019a, htr159c, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc146yz, htr016a, htr019a, htr169c, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc156yz, htr016a, htr019a, htr169c, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc167yz, htr017a, htr019a, htr179c, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd12a, hd69b, htr124a, htr245a, htr456a, htr569a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd14a, hd69b, htr145a, htr245a, htr246a, htr469a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc124yz, htr146b, htr167a, htr246a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd14a, hd79b, htr145a, htr456a, htr567a, htr679a]
    ·
      linarith only [hlam, hd14a, hd69b, htr146a, htr467a, htr567a, htr569a]
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hc124yz, htr145b, htr156a, htr245a, htr456a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd14a, hd59b, htr146a, htr245a, htr246a, htr459a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr124a, htr246a, htr467a, htr679a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd15a, hd69b, htr156a, htr467a, htr469a, htr567a]
    ·
      linarith only [hlam, hc145yz, htr156b, htr167a, htr456a, htr567a]

theorem shard_354 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    : False :=
  proof_shard_354 m htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr019a htr019b htr124a

#print axioms shard_354
end Jsp404.NoSatElevenDBMTerminal
