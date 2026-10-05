import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_567 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr1210c : m.d 1 10 < m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
    linarith only [hlam, htr1210c, htr124b, htr1410b])
  obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr1210c, htr125b, htr1510b])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
    linarith only [hlam, htr1210c, htr126b, htr1610b])
  obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, htr124c, htr1410a, htr2410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc4510yx, htr1210a, htr124a, htr2410b, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr125c, htr1510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc5610yx, htr1210a, htr125a, htr2510b, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, htr126c, htr1610a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc245zy, htr1210a, htr125a, htr2510b, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd02b, hd510a, htr025a, htr256a, htr4510a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 10 (by decide) (by decide) with
    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
  ·
    linarith only [hlam, hd02b, hd56a, htr024a, htr1210a, htr124a, htr2610b, htr5610a]
  ·
    linarith only [hlam, hd02b, hd610a, htr024a, htr245a, htr456a, htr5610a]

theorem shard_567 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr1210c : m.d 1 10 < m.d 1 2)
    : False :=
  proof_shard_567 m htr024a htr025a htr124a htr124b htr124c htr125a htr125b htr125c htr126b htr126c htr1210a htr1210c

#print axioms shard_567
end Jsp404.NoSatElevenDBMTerminal
