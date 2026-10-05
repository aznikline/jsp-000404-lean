import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_496 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, htr012b, htr027a, htr127a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr023b, htr027c, htr037b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr024b, htr027c, htr047b])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr025b, htr027c, htr057b])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr023c, htr037a, htr237a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hc347yx, htr012b, htr023a, htr127a, htr234a, htr237b])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc237yx, htr123b, htr127a, htr134a, htr234a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr024c, htr047a, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc457yx, htr012b, htr024a, htr127a, htr245a, htr247b])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc247yx, htr124b, htr127a, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr025c, htr057a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc234zy, htr124a, htr127a, htr247b, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd01b, hd47a, htr014a, htr145a, htr345a, htr347a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    linarith only [hlam, hc245zy, htr125a, htr127a, htr257b, htr457a]
  ·
    linarith only [hlam, hd01b, hd57a, htr013a, htr134a, htr345a, htr457a]

theorem shard_496 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_496 m htr012b htr013a htr014a htr023a htr023b htr023c htr024a htr024b htr024c htr025b htr025c htr123b htr124a htr124b htr125a htr127a

#print axioms shard_496
end Jsp404.NoSatElevenDBMTerminal
