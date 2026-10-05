import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_054 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, htr124c, htr128b, htr148c])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr125c, htr128b, htr158c])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr126c, htr128b, htr168c])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, htr124b, htr148a, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc458xy, htr124a, htr128a, htr245a, htr248c])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr125b, htr158a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc568xy, htr125a, htr128a, htr256a, htr258c])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr126b, htr168a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc245yz, htr125a, htr128a, htr258c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd02a, hd58b, htr025a, htr256a, htr456a, htr458a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    linarith only [hlam, hd02a, hd68b, htr024a, htr245a, htr456a, htr568a]
  ·
    linarith only [hlam, hd02a, hd56b, htr024a, htr124a, htr128a, htr268c, htr568a]

theorem shard_054 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    : False :=
  proof_shard_054 m htr024a htr025a htr124a htr124b htr124c htr125a htr125b htr125c htr126b htr126c htr128a htr128b

#print axioms shard_054
end Jsp404.NoSatElevenDBMTerminal
