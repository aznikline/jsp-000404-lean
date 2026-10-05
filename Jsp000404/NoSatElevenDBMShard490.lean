import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_490 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd410a := (m.hrange 4 10 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc2310xy, hc2310yx, hc2310yz, hc2310zy⟩ := endpoint_caps m 2 3 10 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc2410xy, hc2410yx, hc2410yz, hc2410zy⟩ := endpoint_caps m 2 4 10 (by decide) (by decide)
  obtain ⟨hc3410xy, hc3410yx, hc3410yz, hc3410zy⟩ := endpoint_caps m 3 4 10 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
    linarith only [hlam, htr012b, htr0210a, htr1210a])
  obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
  have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
    linarith only [hlam, htr0210c, htr023b, htr0310b])
  obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0210c, htr024b, htr0410b])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0210c, htr025b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced2310 := (m.htr 2 3 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2310a, htr2310b, htr2310c, _, _⟩
    linarith only [hlam, htr023c, htr0310a, htr2310a])
  obtain ⟨htr2310a, htr2310b, htr2310c, _, _⟩ := hforced2310
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hc3410yx, htr012b, htr023a, htr1210a, htr2310b, htr234a])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc2310yx, htr1210a, htr123b, htr134a, htr234a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, htr024c, htr0410a, htr2410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc4510yx, htr012b, htr024a, htr1210a, htr2410b, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc2410yx, htr1210a, htr124b, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr025c, htr0510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hc234zy, htr1210a, htr124a, htr2410b, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd01b, hd410a, htr014a, htr145a, htr3410a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 10 (by decide) (by decide) with
    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
  ·
    linarith only [hlam, hc245zy, htr1210a, htr125a, htr2510b, htr4510a]
  ·
    linarith only [hlam, hd01b, hd510a, htr013a, htr134a, htr345a, htr4510a]

theorem shard_490 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_490 m htr012b htr013a htr014a htr023a htr023b htr023c htr024a htr024b htr024c htr025b htr025c htr123b htr124a htr124b htr125a htr1210a

#print axioms shard_490
end Jsp404.NoSatElevenDBMTerminal
