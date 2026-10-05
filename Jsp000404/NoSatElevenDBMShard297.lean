import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_297 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019b : m.d 1 9 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr0110a : m.d 0 1 + lam ≤ m.d 1 10)
    (htr0110b : m.d 0 1 < m.d 0 10)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  have hd17a := (m.hrange 1 7 (by decide)).1
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc179xy, hc179yx, hc179yz, hc179zy⟩ := endpoint_caps m 1 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0110b, htr016c, htr0610c])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0110b, htr017c, htr0710c])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
    linarith only [hlam, htr0110b, htr018c, htr0810c])
  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
    linarith only [hlam, htr0110b, htr019c, htr0910c])
  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
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
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc7810xy, htr0110a, htr017a, htr1710c, htr178a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, hc7910xy, htr0110a, htr017a, htr1710c, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
    linarith only [hlam, htr018b, htr0810a, htr1810a])
  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
    linarith only [hlam, htr019b, htr0910a, htr1910a])
  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
    linarith only [hlam, hc137yz, htr0110a, htr017a, htr1710c, htr3710a])
  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hc146yz, htr0110a, htr016a, htr1610c, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, hc147yz, htr0110a, htr017a, htr1710c, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc167yz, htr0110a, htr017a, htr1710c, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
    linarith only [hlam, hc178yz, htr0110a, htr018a, htr1810c, htr7810a])
  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
    linarith only [hlam, hc179yz, htr0110a, htr019a, htr1910c, htr7910a])
  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd16a, hd710b, htr167a, htr3710a, htr378a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd17a, hd810b, htr179a, htr378a, htr379a, htr7810a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd14a, hd810b, htr146a, htr467a, htr678a, htr7810a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd14a, hd610b, htr147a, htr346a, htr347a, htr4610a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 9 (by decide) (by decide) with
      ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
    ·
      linarith only [hlam, hd13a, hd910b, htr134a, htr347a, htr479a, htr7910a]
    ·
      linarith only [hlam, hd13a, hd710b, htr137a, htr379a, htr4710a, htr479a]
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd13a, hd710b, htr137a, htr378a, htr6710a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd17a, hd910b, htr178a, htr378a, htr379a, htr7910a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc146yz, htr167b, htr178a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd13a, hd710b, htr134a, htr346a, htr467a, htr6710a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd14a, hd710b, htr146a, htr346a, htr347a, htr4710a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 9 (by decide) (by decide) with
      ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
    ·
      linarith only [hlam, hd14a, hd710b, htr147a, htr3710a, htr379a, htr479a]
    ·
      linarith only [hlam, hc134yz, htr147b, htr179a, htr347a, htr479a]

theorem shard_297 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019b : m.d 1 9 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr0110a : m.d 0 1 + lam ≤ m.d 1 10)
    (htr0110b : m.d 0 1 < m.d 0 10)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    : False :=
  proof_shard_297 m htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr019b htr019c htr0110a htr0110b htr134a htr137a htr146a htr146b htr147a htr147b

#print axioms shard_297
end Jsp404.NoSatElevenDBMTerminal
