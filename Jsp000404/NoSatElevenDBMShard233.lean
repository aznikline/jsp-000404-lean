import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_233 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  have hd410a := (m.hrange 4 10 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc2310xy, hc2310yx, hc2310yz, hc2310zy⟩ := endpoint_caps m 2 3 10 (by decide) (by decide)
  obtain ⟨hc3410xy, hc3410yx, hc3410yz, hc3410zy⟩ := endpoint_caps m 3 4 10 (by decide) (by decide)
  obtain ⟨hc3510xy, hc3510yx, hc3510yz, hc3510zy⟩ := endpoint_caps m 3 5 10 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
    linarith only [hlam, htr0110c, htr012b, htr0210b])
  obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
  have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
    linarith only [hlam, htr0110c, htr013b, htr0310b])
  obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0110c, htr014b, htr0410b])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0110c, htr015b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0110c, htr016b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced1210 := (m.htr 1 2 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1210a, htr1210b, htr1210c, _, _⟩
    linarith only [hlam, htr012c, htr0210a, htr1210a])
  obtain ⟨htr1210a, htr1210b, htr1210c, _, _⟩ := hforced1210
  have hforced123 := (m.htr 1 2 3 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr123a, htr123b, htr123c, _, _⟩
    linarith only [hlam, hc2310yx, htr0110a, htr012a, htr1210b, htr123a])
  obtain ⟨htr123a, htr123b, htr123c, _, _⟩ := hforced123
  have hforced1310 := (m.htr 1 3 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1310a, htr1310b, htr1310c, _, _⟩
    linarith only [hlam, htr013c, htr0310a, htr1310a])
  obtain ⟨htr1310a, htr1310b, htr1310c, _, _⟩ := hforced1310
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc3410yx, htr0110a, htr013a, htr1310b, htr134a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc3510yx, htr0110a, htr013a, htr1310b, htr135a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
    linarith only [hlam, htr014c, htr0410a, htr1410a])
  obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc4510yx, htr0110a, htr014a, htr1410b, htr145a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr015c, htr0510a, htr1510a])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc5610yx, htr0110a, htr015a, htr1510b, htr156a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
    linarith only [hlam, htr016c, htr0610a, htr1610a])
  obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hc134zy, htr0110a, htr014a, htr1410b, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, hc135zy, htr0110a, htr015a, htr1510b, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc145zy, htr0110a, htr015a, htr1510b, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc156zy, htr0110a, htr016a, htr1610b, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  rcases m.htr 2 3 4 (by decide) (by decide) with
    ⟨htr234a, htr234b, htr234c, _, _⟩ | ⟨htr234a, htr234b, htr234c, _, _⟩
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13b, hd510a, htr134a, htr234a, htr235a, htr3510a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hc123zy, htr134c, htr145a, htr234a, htr345a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr156a, htr235a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd13b, hd510a, htr135a, htr356a, htr4510a, htr456a]
    ·
      linarith only [hlam, hd13b, hd610a, htr134a, htr345a, htr456a, htr5610a]
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13b, hd410a, htr135a, htr234a, htr235a, htr3410a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hd12b, hd510a, htr123a, htr234a, htr345a, htr4510a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd12b, hd610a, htr123a, htr235a, htr356a, htr5610a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a]
    ·
      linarith only [hlam, hd14b, hd510a, htr145a, htr3510a, htr356a, htr456a]

theorem shard_233 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    : False :=
  proof_shard_233 m htr012a htr012b htr012c htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr0110a htr0110c

#print axioms shard_233
end Jsp404.NoSatElevenDBMTerminal
