import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_290 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < 4*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < 4*lam := by
    linarith only [hd16braw, hp]
  have hd610a := (m.hrange 6 10 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
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
  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
    linarith only [hlam, htr0110c, htr018b, htr0810b])
  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr015c, htr0510a, htr1510a])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc5610yx, htr0110a, htr015a, htr1510b, htr156a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc5710yx, htr0110a, htr015a, htr1510b, htr157a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
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
  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
    linarith only [hlam, htr018c, htr0810a, htr1810a])
  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc156zy, htr0110a, htr016a, htr1610b, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
    linarith only [hlam, hc157zy, htr0110a, htr017a, htr1710b, htr5710a])
  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
    linarith only [hlam, hc167zy, htr0110a, htr017a, htr1710b, htr6710a])
  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
    linarith only [hlam, hc178zy, htr0110a, htr018a, htr1810b, htr7810a])
  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc125zy, htr156c, htr167a, htr256a, htr567a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd15b, hd610a, htr157a, htr256a, htr257a, htr5610a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd12b, hd810a, htr125a, htr257a, htr578a, htr7810a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hc156zy, htr167c, htr178a, htr567a, htr678a]
    ·
      linarith only [hlam, hd16b, hd710a, htr167a, htr5710a, htr578a, htr678a]
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd12b, hd710a, htr125a, htr256a, htr567a, htr6710a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd15b, hd710a, htr156a, htr256a, htr257a, htr5710a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc125zy, htr157c, htr178a, htr257a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd15b, hd710a, htr157a, htr578a, htr6710a, htr678a]
    ·
      linarith only [hlam, hd15b, hd810a, htr156a, htr567a, htr678a, htr7810a]

theorem shard_290 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr0110a : m.d 1 10 + lam ≤ m.d 0 1)
    (htr0110c : m.d 0 10 < m.d 0 1)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_290 m htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr0110a htr0110c htr125a

#print axioms shard_290
end Jsp404.NoSatElevenDBMTerminal
