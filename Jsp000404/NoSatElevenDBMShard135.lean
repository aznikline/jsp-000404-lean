import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_135 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr0210a : m.d 0 2 + lam ≤ m.d 2 10)
    (htr0210b : m.d 0 2 < m.d 0 10)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd410a, hd410braw⟩ := m.hrange 4 10 (by decide)
  have hd410b : m.d 4 10 < 4*lam := by
    linarith only [hd410braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0210b, htr024c, htr0410c])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0210b, htr025c, htr0510c])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0210b, htr026c, htr0610c])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr0210a, htr023a, htr1210a, htr234a])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr235a, htr235b, htr235c, _, _⟩
    linarith only [hlam, hd12b, hd35a, htr0210a, htr023a, htr1210a, htr235a])
  obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr0210a, htr024a, htr1210a, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, htr024b, htr0410a, htr2410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr0210a, htr025a, htr1210a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr025b, htr0510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, htr026b, htr0610a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hc234yz, htr0210a, htr024a, htr2410c, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, hc235yz, htr0210a, htr025a, htr2510c, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc245yz, htr0210a, htr025a, htr2510c, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc256yz, htr0210a, htr026a, htr2610c, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  rcases m.htr 3 4 5 (by decide) (by decide) with
    ⟨htr345a, htr345b, htr345c, _, _⟩ | ⟨htr345a, htr345b, htr345c, _, _⟩
  ·
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hd01a, hd510b, htr013a, htr134a, htr345a, htr4510a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd23a, hd510b, htr134a, htr135a, htr234a, htr3510a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc123zy, htr135a, htr235b, htr256a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd23a, hd610b, htr234a, htr345a, htr456a, htr5610a]
    ·
      linarith only [hlam, hd23a, hd510b, htr235a, htr356a, htr4510a, htr456a]
  ·
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr234b, htr245a, htr345a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd23a, hd410b, htr134a, htr135a, htr235a, htr3410a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd01a, hd610b, htr013a, htr135a, htr356a, htr5610a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd24a, hd510b, htr245a, htr3510a, htr356a, htr456a]
    ·
      linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a]

theorem shard_135 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr0210a : m.d 0 2 + lam ≤ m.d 2 10)
    (htr0210b : m.d 0 2 < m.d 0 10)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_135 m htr013a htr023a htr024a htr024b htr024c htr025a htr025b htr025c htr026a htr026b htr026c htr0210a htr0210b htr1210a

#print axioms shard_135
end Jsp404.NoSatElevenDBMTerminal
