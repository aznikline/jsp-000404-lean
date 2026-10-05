import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_085 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr129b : m.d 1 2 < m.d 1 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd49a, hd49braw⟩ := m.hrange 4 9 (by decide)
  have hd49b : m.d 4 9 < 4*lam := by
    linarith only [hd49braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr124c, htr129b, htr149c])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr125c, htr129b, htr159c])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, htr124b, htr149a, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc459xy, htr124a, htr129a, htr245a, htr249c])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, htr125b, htr159a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hc234yz, htr124a, htr129a, htr249c, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd02a, hd49b, htr024a, htr245a, htr345a, htr349a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 9 (by decide) (by decide) with
    ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
  ·
    linarith only [hlam, hd02a, hd59b, htr023a, htr234a, htr345a, htr459a]
  ·
    linarith only [hlam, hd02a, hd45b, htr023a, htr123a, htr129a, htr259c, htr459a]

theorem shard_085 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr129b : m.d 1 2 < m.d 1 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_085 m htr023a htr024a htr123a htr124a htr124b htr124c htr125b htr125c htr129a htr129b htr234a

#print axioms shard_085
end Jsp404.NoSatElevenDBMTerminal
