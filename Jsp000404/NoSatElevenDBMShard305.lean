import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_305 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr0110a : m.d 0 1 + lam ≤ m.d 1 10)
    (htr0110b : m.d 0 1 < m.d 0 10)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc3410xy, hc3410yx, hc3410yz, hc3410zy⟩ := endpoint_caps m 3 4 10 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc4610xy, hc4610yx, hc4610yz, hc4610zy⟩ := endpoint_caps m 4 6 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
    linarith only [hlam, htr0110b, htr013c, htr0310c])
  obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0110b, htr014c, htr0410c])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
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
  have hforced1310 := (m.htr 1 3 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1310a, htr1310b, htr1310c, _, _⟩
    linarith only [hlam, htr013b, htr0310a, htr1310a])
  obtain ⟨htr1310a, htr1310b, htr1310c, _, _⟩ := hforced1310
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc3410xy, htr0110a, htr013a, htr1310c, htr134a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
    linarith only [hlam, htr014b, htr0410a, htr1410a])
  obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc4510xy, htr0110a, htr014a, htr1410c, htr145a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc4610xy, htr0110a, htr014a, htr1410c, htr146a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
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
  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
    linarith only [hlam, htr017b, htr0710a, htr1710a])
  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc145yz, htr0110a, htr015a, htr1510c, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hc146yz, htr0110a, htr016a, htr1610c, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc156yz, htr0110a, htr016a, htr1610c, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc167yz, htr0110a, htr017a, htr1710c, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  rcases m.htr 3 4 5 (by decide) (by decide) with
    ⟨htr345a, htr345b, htr345c, _, _⟩ | ⟨htr345a, htr345b, htr345c, _, _⟩
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd14a, hd510b, htr146a, htr345a, htr346a, htr4510a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hd13a, hd610b, htr134a, htr345a, htr456a, htr5610a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd13a, hd710b, htr134a, htr346a, htr467a, htr6710a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd15a, hd610b, htr156a, htr4610a, htr467a, htr567a]
    ·
      linarith only [hlam, hc145yz, htr156b, htr167a, htr456a, htr567a]
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd14a, hd610b, htr145a, htr345a, htr346a, htr4610a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr156a, htr345a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd14a, hd710b, htr145a, htr456a, htr567a, htr6710a]
    ·
      linarith only [hlam, hd14a, hd610b, htr146a, htr467a, htr5610a, htr567a]

theorem shard_305 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr0110a : m.d 0 1 + lam ≤ m.d 1 10)
    (htr0110b : m.d 0 1 < m.d 0 10)
    : False :=
  proof_shard_305 m htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr0110a htr0110b

#print axioms shard_305
end Jsp404.NoSatElevenDBMTerminal
