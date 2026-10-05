import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_251 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 1 9)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137c : m.d 1 7 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < 4*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < 4*lam := by
    linarith only [hd17braw, hp]
  have hd610a := (m.hrange 6 10 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  have hd810a := (m.hrange 8 10 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc179xy, hc179yx, hc179yz, hc179zy⟩ := endpoint_caps m 1 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0110c, htr016b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0110c, htr017b, htr0710b])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
    linarith only [hlam, htr0110c, htr018b, htr0810b])
  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
    linarith only [hlam, htr0110c, htr019b, htr0910b])
  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
  have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
    linarith only [hlam, htr016c, htr0610a, htr1610a])
  obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc6710yx, htr0110a, htr016a, htr1610b, htr167a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
    linarith only [hlam, htr017c, htr0710a, htr1710a])
  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc7810yx, htr0110a, htr017a, htr1710b, htr178a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, hc7910yx, htr0110a, htr017a, htr1710b, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
    linarith only [hlam, htr018c, htr0810a, htr1810a])
  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
    linarith only [hlam, htr019c, htr0910a, htr1910a])
  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
    linarith only [hlam, hc127zy, htr0110a, htr017a, htr1710b, htr2710a])
  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hc136zy, htr0110a, htr016a, htr1610b, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
    linarith only [hlam, hc137zy, htr0110a, htr017a, htr1710b, htr3710a])
  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc167zy, htr0110a, htr017a, htr1710b, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
    linarith only [hlam, hc178zy, htr0110a, htr018a, htr1810b, htr7810a])
  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
    linarith only [hlam, hc179zy, htr0110a, htr019a, htr1910b, htr7910a])
  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd12b, hd710a, htr127a, htr278a, htr6710a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd17b, hd910a, htr178a, htr278a, htr279a, htr7910a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc136zy, htr167c, htr178a, htr367a, htr678a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd13b, hd710a, htr136a, htr236a, htr237a, htr3710a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    rcases m.htr 3 7 9 (by decide) (by decide) with
      ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
    ·
      linarith only [hlam, hc123zy, htr137c, htr179a, htr237a, htr379a]
    ·
      linarith only [hlam, hd13b, hd710a, htr137a, htr2710a, htr279a, htr379a]
  ·
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd16b, hd710a, htr167a, htr2710a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd17b, hd810a, htr179a, htr278a, htr279a, htr7810a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd13b, hd810a, htr136a, htr367a, htr678a, htr7810a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hc123zy, htr136c, htr167a, htr236a, htr367a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd13b, hd610a, htr137a, htr236a, htr237a, htr3610a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    rcases m.htr 3 7 9 (by decide) (by decide) with
      ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
    ·
      linarith only [hlam, hd12b, hd710a, htr127a, htr279a, htr3710a, htr379a]
    ·
      linarith only [hlam, hd12b, hd910a, htr123a, htr237a, htr379a, htr7910a]

theorem shard_251 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr019c : m.d 0 9 < m.d 1 9)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137c : m.d 1 7 < m.d 1 3)
    : False :=
  proof_shard_251 m htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr019b htr019c htr0110a htr0110c htr123a htr127a htr136a htr136c htr137a htr137c

#print axioms shard_251
end Jsp404.NoSatElevenDBMTerminal
