import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_560 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd510a := (m.hrange 5 10 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
    linarith only [hlam, htr012b, htr0210a, htr1210a])
  obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0210c, htr024b, htr0410b])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0210c, htr025b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0210c, htr026b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
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
    linarith only [hlam, hc234xy, htr123a, htr124b, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr025c, htr0510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc5610yx, htr012b, htr025a, htr1210a, htr2510b, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc235xy, htr123a, htr125b, htr156a, htr256a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, htr026c, htr0610a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc245zy, htr1210a, htr125a, htr2510b, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd01b, hd510a, htr015a, htr156a, htr4510a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 10 (by decide) (by decide) with
    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
  ·
    linarith only [hlam, hc256zy, htr1210a, htr126a, htr2610b, htr5610a]
  ·
    linarith only [hlam, hd01b, hd610a, htr014a, htr145a, htr456a, htr5610a]

theorem shard_560 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_560 m htr012b htr014a htr015a htr024a htr024b htr024c htr025a htr025b htr025c htr026b htr026c htr123a htr124b htr125a htr125b htr126a htr1210a

#print axioms shard_560
end Jsp404.NoSatElevenDBMTerminal
