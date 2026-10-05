import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_489 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr029a : m.d 2 9 + lam ≤ m.d 0 2)
    (htr029c : m.d 0 9 < m.d 0 2)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  have hd49a := (m.hrange 4 9 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr024b, htr029c, htr049b])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr025b, htr029c, htr059b])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr026b, htr029c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hd12a, hd34b, htr023a, htr029a, htr129a, htr234a])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr235a, htr235b, htr235c, _, _⟩
    linarith only [hlam, hd12a, hd35b, htr023a, htr029a, htr129a, htr235a])
  obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr024a, htr029a, htr129a, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, htr024c, htr049a, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr025a, htr029a, htr129a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, htr025c, htr059a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, htr026c, htr069a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hc234zy, htr024a, htr029a, htr249b, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc235zy, htr025a, htr029a, htr259b, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc245zy, htr025a, htr029a, htr259b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc256zy, htr026a, htr029a, htr269b, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  rcases m.htr 3 4 5 (by decide) (by decide) with
    ⟨htr345a, htr345b, htr345c, _, _⟩ | ⟨htr345a, htr345b, htr345c, _, _⟩
  ·
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr234c, htr245a, htr345a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd23b, hd49a, htr134a, htr135a, htr235a, htr349a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd01b, hd69a, htr013a, htr135a, htr356a, htr569a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a]
    ·
      linarith only [hlam, hd24b, hd59a, htr245a, htr356a, htr359a, htr456a]
  ·
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hd01b, hd59a, htr013a, htr134a, htr345a, htr459a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd23b, hd59a, htr134a, htr135a, htr234a, htr359a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc123yz, htr135a, htr235c, htr256a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd23b, hd59a, htr235a, htr356a, htr456a, htr459a]
    ·
      linarith only [hlam, hd23b, hd69a, htr234a, htr345a, htr456a, htr569a]

theorem shard_489 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr029a : m.d 2 9 + lam ≤ m.d 0 2)
    (htr029c : m.d 0 9 < m.d 0 2)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    : False :=
  proof_shard_489 m htr013a htr023a htr024a htr024b htr024c htr025a htr025b htr025c htr026a htr026b htr026c htr029a htr029c htr129a

#print axioms shard_489
end Jsp404.NoSatElevenDBMTerminal
