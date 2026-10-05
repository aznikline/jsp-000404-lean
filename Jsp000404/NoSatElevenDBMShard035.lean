import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_035 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019c : m.d 0 9 < m.d 1 9)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr029b : m.d 0 2 < m.d 0 9)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128c : m.d 1 8 < m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr129c : m.d 1 9 < m.d 2 9)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247c : m.d 2 7 < m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  obtain ⟨hd27a, hd27braw⟩ := m.hrange 2 7 (by decide)
  have hd27b : m.d 2 7 < 4*lam := by
    linarith only [hd27braw, hp]
  have hd610a := (m.hrange 6 10 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  have hd810a := (m.hrange 8 10 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
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
  have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
    linarith only [hlam, hc235yx, htr0210a, htr025a, htr1210a, htr123a])
  obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0210c, htr026b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0210c, htr027b, htr0710b])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
    linarith only [hlam, htr0210c, htr028b, htr0810b])
  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
    linarith only [hlam, htr0210c, htr029b, htr0910b])
  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, htr016c, htr0610a, htr126c, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc6710yx, htr012c, htr0210a, htr126a, htr2610b, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
    linarith only [hlam, htr017c, htr0710a, htr127c, htr2710a])
  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc7810yx, htr012c, htr0210a, htr127a, htr2710b, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hc7910yx, htr012c, htr0210a, htr127a, htr2710b, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
    linarith only [hlam, htr018c, htr0810a, htr128c, htr2810a])
  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
    linarith only [hlam, htr019c, htr0910a, htr129c, htr2910a])
  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
    linarith only [hlam, hc237zy, htr1210a, htr127a, htr2710b, htr3710a])
  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hc246zy, htr1210a, htr126a, htr2610b, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, hc247zy, htr1210a, htr127a, htr2710b, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc267zy, htr1210a, htr127a, htr2710b, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
    linarith only [hlam, hc278zy, htr1210a, htr128a, htr2810b, htr7810a])
  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
    linarith only [hlam, hc279zy, htr1210a, htr129a, htr2910b, htr7910a])
  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd23b, hd710a, htr237a, htr378a, htr6710a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd27b, hd910a, htr278a, htr378a, htr379a, htr7910a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246zy, htr267c, htr278a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd23b, hd710a, htr234a, htr346a, htr467a, htr6710a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd24b, hd710a, htr246a, htr346a, htr347a, htr4710a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 9 (by decide) (by decide) with
      ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
    ·
      linarith only [hlam, hc234zy, htr247c, htr279a, htr347a, htr479a]
    ·
      linarith only [hlam, hd24b, hd710a, htr247a, htr3710a, htr379a, htr479a]
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd26b, hd710a, htr267a, htr3710a, htr378a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd27b, hd810a, htr279a, htr378a, htr379a, htr7810a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd24b, hd810a, htr246a, htr467a, htr678a, htr7810a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd24b, hd610a, htr247a, htr346a, htr347a, htr4610a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 4 7 9 (by decide) (by decide) with
      ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
    ·
      linarith only [hlam, hd23b, hd710a, htr237a, htr379a, htr4710a, htr479a]
    ·
      linarith only [hlam, hd23b, hd910a, htr234a, htr347a, htr479a, htr7910a]

theorem shard_035 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019c : m.d 0 9 < m.d 1 9)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr029b : m.d 0 2 < m.d 0 9)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128c : m.d 1 8 < m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr129c : m.d 1 9 < m.d 2 9)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247c : m.d 2 7 < m.d 2 4)
    : False :=
  proof_shard_035 m htr012c htr016c htr017c htr018c htr019c htr025a htr026b htr027b htr028b htr029b htr123a htr126a htr126c htr127a htr127c htr128a htr128c htr129a htr129c htr1210a htr234a htr237a htr246a htr246c htr247a htr247c

#print axioms shard_035
end Jsp404.NoSatElevenDBMTerminal
