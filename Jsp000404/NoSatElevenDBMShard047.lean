import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_047 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128c : m.d 1 8 < m.d 2 8)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  have hd610a := (m.hrange 6 10 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
    linarith only [hlam, hc234yx, htr0210a, htr024a, htr1210a, htr123a])
  obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0210c, htr025b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
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
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr015c, htr0510a, htr125c, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc5610yx, htr012c, htr0210a, htr125a, htr2510b, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc5710yx, htr012c, htr0210a, htr125a, htr2510b, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
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
  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
    linarith only [hlam, htr018c, htr0810a, htr128c, htr2810a])
  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc256zy, htr1210a, htr126a, htr2610b, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
    linarith only [hlam, hc257zy, htr1210a, htr127a, htr2710b, htr5710a])
  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc267zy, htr1210a, htr127a, htr2710b, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
    linarith only [hlam, hc278zy, htr1210a, htr128a, htr2810b, htr7810a])
  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc235zy, htr256c, htr267a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25b, hd610a, htr257a, htr356a, htr357a, htr5610a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd23b, hd810a, htr235a, htr357a, htr578a, htr7810a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a]
    ·
      linarith only [hlam, hd26b, hd710a, htr267a, htr5710a, htr578a, htr678a]
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd23b, hd710a, htr235a, htr356a, htr567a, htr6710a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25b, hd710a, htr256a, htr356a, htr357a, htr5710a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc235zy, htr257c, htr278a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd25b, hd710a, htr257a, htr578a, htr6710a, htr678a]
    ·
      linarith only [hlam, hd25b, hd810a, htr256a, htr567a, htr678a, htr7810a]

theorem shard_047 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128c : m.d 1 8 < m.d 2 8)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_047 m htr012c htr015c htr016c htr017c htr018c htr024a htr025b htr026b htr027b htr028b htr123a htr125a htr125c htr126a htr126c htr127a htr127c htr128a htr128c htr1210a htr235a

#print axioms shard_047
end Jsp404.NoSatElevenDBMTerminal
