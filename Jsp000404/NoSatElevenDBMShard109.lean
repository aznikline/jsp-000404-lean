import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_109 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr024b, htr028c, htr048b])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr025b, htr028c, htr058b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
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
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr023a, htr028a, htr123a, htr248b, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd12b, hd48a, htr124a, htr245a, htr345a, htr348a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 8 (by decide) (by decide) with
    ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
  ·
    linarith only [hlam, hd12b, hd45a, htr023a, htr028a, htr123a, htr258b, htr458a]
  ·
    linarith only [hlam, hd12b, hd58a, htr123a, htr234a, htr345a, htr458a]

theorem shard_109 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_109 m htr023a htr024a htr024b htr024c htr025b htr025c htr028a htr028c htr123a htr124a htr234a

#print axioms shard_109
end Jsp404.NoSatElevenDBMTerminal
