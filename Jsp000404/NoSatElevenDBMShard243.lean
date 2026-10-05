import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_243 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 1 9)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < 4*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < 4*lam := by
    linarith only [hd16braw, hp]
  have hd510a := (m.hrange 5 10 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc169xy, hc169yx, hc169yz, hc169zy⟩ := endpoint_caps m 1 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0110c, htr015b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0110c, htr016b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0110c, htr017b, htr0710b])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
    linarith only [hlam, htr0110c, htr019b, htr0910b])
  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
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
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc6710yx, htr0110a, htr016a, htr1610b, htr167a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hc6910yx, htr0110a, htr016a, htr1610b, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
    linarith only [hlam, htr017c, htr0710a, htr1710a])
  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
    linarith only [hlam, htr019c, htr0910a, htr1910a])
  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hc126zy, htr0110a, htr016a, htr1610b, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, hc135zy, htr0110a, htr015a, htr1510b, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hc136zy, htr0110a, htr016a, htr1610b, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc156zy, htr0110a, htr016a, htr1610b, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc167zy, htr0110a, htr017a, htr1710b, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
    linarith only [hlam, hc169zy, htr0110a, htr019a, htr1910b, htr6910a])
  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd12b, hd610a, htr126a, htr267a, htr5610a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd16b, hd910a, htr167a, htr267a, htr269a, htr6910a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc135zy, htr156c, htr167a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd12b, hd610a, htr123a, htr235a, htr356a, htr5610a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13b, hd610a, htr135a, htr235a, htr236a, htr3610a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 9 (by decide) (by decide) with
      ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
    ·
      linarith only [hlam, hc123zy, htr136c, htr169a, htr236a, htr369a]
    ·
      linarith only [hlam, hd13b, hd610a, htr136a, htr2610a, htr269a, htr369a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd15b, hd610a, htr156a, htr2610a, htr267a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd16b, hd710a, htr169a, htr267a, htr269a, htr6710a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd13b, hd710a, htr135a, htr356a, htr567a, htr6710a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr156a, htr235a, htr356a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13b, hd510a, htr136a, htr235a, htr236a, htr3510a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 9 (by decide) (by decide) with
      ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
    ·
      linarith only [hlam, hd12b, hd610a, htr126a, htr269a, htr3610a, htr369a]
    ·
      linarith only [hlam, hd12b, hd910a, htr123a, htr236a, htr369a, htr6910a]

theorem shard_243 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 1 9)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    : False :=
  proof_shard_243 m htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr019a htr019b htr019c htr0110a htr0110c htr123a htr126a htr135a htr135c htr136a htr136c

#print axioms shard_243
end Jsp404.NoSatElevenDBMTerminal
