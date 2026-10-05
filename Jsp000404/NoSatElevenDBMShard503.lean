import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_503 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr029a : m.d 0 2 + lam ≤ m.d 2 9)
    (htr029b : m.d 0 2 < m.d 0 9)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr024c, htr029b, htr049c])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr025c, htr029b, htr059c])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr026c, htr029b, htr069c])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, htr024b, htr049a, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc459xy, htr024a, htr029a, htr245a, htr249c])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, htr025b, htr059a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc569xy, htr025a, htr029a, htr256a, htr259c])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, htr026b, htr069a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr024a, htr029a, htr124a, htr259c, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12a, hd59b, htr125a, htr256a, htr456a, htr459a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 9 (by decide) (by decide) with
    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
  ·
    linarith only [hlam, hd12a, hd69b, htr124a, htr245a, htr456a, htr569a]
  ·
    linarith only [hlam, hd12a, hd56b, htr024a, htr029a, htr124a, htr269c, htr569a]

theorem shard_503 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr029a : m.d 0 2 + lam ≤ m.d 2 9)
    (htr029b : m.d 0 2 < m.d 0 9)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    : False :=
  proof_shard_503 m htr024a htr024b htr024c htr025a htr025b htr025c htr026b htr026c htr029a htr029b htr124a htr125a

#print axioms shard_503
end Jsp404.NoSatElevenDBMTerminal
