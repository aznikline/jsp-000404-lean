import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_568 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr129c : m.d 1 9 < m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr124b, htr129c, htr149b])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr125b, htr129c, htr159b])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr126b, htr129c, htr169b])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, htr124c, htr149a, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc459yx, htr124a, htr129a, htr245a, htr249b])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, htr125c, htr159a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc569yx, htr125a, htr129a, htr256a, htr259b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, htr126c, htr169a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc245zy, htr125a, htr129a, htr259b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd02b, hd59a, htr025a, htr256a, htr456a, htr459a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 9 (by decide) (by decide) with
    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
  ·
    linarith only [hlam, hd02b, hd56a, htr024a, htr124a, htr129a, htr269b, htr569a]
  ·
    linarith only [hlam, hd02b, hd69a, htr024a, htr245a, htr456a, htr569a]

theorem shard_568 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr129c : m.d 1 9 < m.d 1 2)
    : False :=
  proof_shard_568 m htr024a htr025a htr124a htr124b htr124c htr125a htr125b htr125c htr126b htr126c htr129a htr129c

#print axioms shard_568
end Jsp404.NoSatElevenDBMTerminal
