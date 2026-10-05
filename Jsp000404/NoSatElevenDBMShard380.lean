import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_380 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019b : m.d 1 9 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr0110a : m.d 0 1 + lam ≤ m.d 1 10)
    (htr0110b : m.d 0 1 < m.d 0 10)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
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
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0110b, htr015c, htr0510c])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0110b, htr016c, htr0610c])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0110b, htr017c, htr0710c])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
    linarith only [hlam, htr0110b, htr019c, htr0910c])
  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr015b, htr0510a, htr1510a])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc5610xy, htr0110a, htr015a, htr1510c, htr156a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
    linarith only [hlam, htr016b, htr0610a, htr1610a])
  obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc6710xy, htr0110a, htr016a, htr1610c, htr167a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hc6910xy, htr0110a, htr016a, htr1610c, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
    linarith only [hlam, htr017b, htr0710a, htr1710a])
  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
    linarith only [hlam, htr019b, htr0910a, htr1910a])
  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hc126yz, htr0110a, htr016a, htr1610c, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, hc135yz, htr0110a, htr015a, htr1510c, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hc136yz, htr0110a, htr016a, htr1610c, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc156yz, htr0110a, htr016a, htr1610c, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc167yz, htr0110a, htr017a, htr1710c, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
    linarith only [hlam, hc169yz, htr0110a, htr019a, htr1910c, htr6910a])
  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd15a, hd610b, htr156a, htr2610a, htr267a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd16a, hd710b, htr169a, htr267a, htr269a, htr6710a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd13a, hd710b, htr135a, htr356a, htr567a, htr6710a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13a, hd510b, htr136a, htr235a, htr236a, htr3510a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 9 (by decide) (by decide) with
      ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
    ·
      linarith only [hlam, hd12a, hd910b, htr123a, htr236a, htr369a, htr6910a]
    ·
      linarith only [hlam, hd12a, hd610b, htr126a, htr269a, htr3610a, htr369a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd12a, hd610b, htr126a, htr267a, htr5610a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd16a, hd910b, htr167a, htr267a, htr269a, htr6910a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc135yz, htr156b, htr167a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd12a, hd610b, htr123a, htr235a, htr356a, htr5610a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13a, hd610b, htr135a, htr235a, htr236a, htr3610a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 9 (by decide) (by decide) with
      ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
    ·
      linarith only [hlam, hd13a, hd610b, htr136a, htr2610a, htr269a, htr369a]
    ·
      linarith only [hlam, hc123yz, htr136b, htr169a, htr236a, htr369a]

theorem shard_380 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019b : m.d 1 9 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr0110a : m.d 0 1 + lam ≤ m.d 1 10)
    (htr0110b : m.d 0 1 < m.d 0 10)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    : False :=
  proof_shard_380 m htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr019a htr019b htr019c htr0110a htr0110b htr123a htr126a htr135a htr135b htr136a htr136b

#print axioms shard_380
end Jsp404.NoSatElevenDBMTerminal
