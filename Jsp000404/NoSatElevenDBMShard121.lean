import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_121 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr024b, htr028c, htr048b])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr025b, htr028c, htr058b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr026b, htr028c, htr068b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, htr024c, htr048a, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc458yx, htr024a, htr028a, htr245a, htr248b])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr025c, htr058a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc568yx, htr025a, htr028a, htr256a, htr258b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr026c, htr068a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr024a, htr028a, htr124a, htr258b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr125a, htr256a, htr456a, htr458a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    linarith only [hlam, hd12b, hd56a, htr024a, htr028a, htr124a, htr268b, htr568a]
  ·
    linarith only [hlam, hd12b, hd68a, htr124a, htr245a, htr456a, htr568a]

theorem shard_121 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_121 m htr024a htr024b htr024c htr025a htr025b htr025c htr026b htr026c htr028a htr028c htr124a htr125a

#print axioms shard_121
end Jsp404.NoSatElevenDBMTerminal
