import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_588 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr019b : m.d 1 9 < m.d 0 9)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr029c : m.d 0 9 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr129b : m.d 2 9 < m.d 1 9)
    (htr1210a : m.d 1 2 + lam ≤ m.d 2 10)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
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
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc279xy, hc279yx, hc279yz, hc279zy⟩ := endpoint_caps m 2 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
    linarith only [hlam, hc235xy, htr0210a, htr025a, htr1210a, htr123a])
  obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0210b, htr026c, htr0610c])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0210b, htr027c, htr0710c])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
    linarith only [hlam, htr0210b, htr028c, htr0810c])
  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
    linarith only [hlam, htr0210b, htr029c, htr0910c])
  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, htr016b, htr0610a, htr126b, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc6710xy, htr012b, htr0210a, htr126a, htr2610c, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
    linarith only [hlam, htr017b, htr0710a, htr127b, htr2710a])
  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc7810xy, htr012b, htr0210a, htr127a, htr2710c, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hc7910xy, htr012b, htr0210a, htr127a, htr2710c, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
    linarith only [hlam, htr018b, htr0810a, htr128b, htr2810a])
  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
    linarith only [hlam, htr019b, htr0910a, htr129b, htr2910a])
  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
    linarith only [hlam, hc237yz, htr1210a, htr127a, htr2710c, htr3710a])
  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hc246yz, htr1210a, htr126a, htr2610c, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, hc247yz, htr1210a, htr127a, htr2710c, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc267yz, htr1210a, htr127a, htr2710c, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
    linarith only [hlam, hc278yz, htr1210a, htr128a, htr2810c, htr7810a])
  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
    linarith only [hlam, hc279yz, htr1210a, htr129a, htr2910c, htr7910a])
  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd26a, hd710b, htr267a, htr3710a, htr378a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd27a, hd810b, htr279a, htr378a, htr379a, htr7810a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd24a, hd810b, htr246a, htr467a, htr678a, htr7810a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd24a, hd610b, htr247a, htr346a, htr347a, htr4610a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 9 (by decide) (by decide) with
      ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
    ·
      linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a]
    ·
      linarith only [hlam, hd23a, hd710b, htr237a, htr379a, htr4710a, htr479a]
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd23a, hd710b, htr237a, htr378a, htr6710a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd27a, hd910b, htr278a, htr378a, htr379a, htr7910a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd23a, hd710b, htr234a, htr346a, htr467a, htr6710a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd24a, hd710b, htr246a, htr346a, htr347a, htr4710a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 9 (by decide) (by decide) with
      ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
    ·
      linarith only [hlam, hd24a, hd710b, htr247a, htr3710a, htr379a, htr479a]
    ·
      linarith only [hlam, hc234yz, htr247b, htr279a, htr347a, htr479a]

theorem shard_588 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr019b : m.d 1 9 < m.d 0 9)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr029c : m.d 0 9 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr129b : m.d 2 9 < m.d 1 9)
    (htr1210a : m.d 1 2 + lam ≤ m.d 2 10)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    : False :=
  proof_shard_588 m htr012b htr016b htr017b htr018b htr019b htr025a htr026c htr027c htr028c htr029c htr123a htr126a htr126b htr127a htr127b htr128a htr128b htr129a htr129b htr1210a htr234a htr237a htr246a htr246b htr247a htr247b

#print axioms shard_588
end Jsp404.NoSatElevenDBMTerminal
