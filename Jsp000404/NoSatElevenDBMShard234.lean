import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_234 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019c : m.d 0 9 < m.d 0 1)
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
  have hd49a := (m.hrange 4 9 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc239xy, hc239yx, hc239yz, hc239zy⟩ := endpoint_caps m 2 3 9 (by decide) (by decide)
  obtain ⟨hc349xy, hc349yx, hc349yz, hc349zy⟩ := endpoint_caps m 3 4 9 (by decide) (by decide)
  obtain ⟨hc359xy, hc359yx, hc359yz, hc359zy⟩ := endpoint_caps m 3 5 9 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  have hforced029 := (m.htr 0 2 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr029a, htr029b, htr029c, _, _⟩
    linarith only [hlam, htr012b, htr019c, htr029b])
  obtain ⟨htr029a, htr029b, htr029c, _, _⟩ := hforced029
  have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr039a, htr039b, htr039c, _, _⟩
    linarith only [hlam, htr013b, htr019c, htr039b])
  obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr014b, htr019c, htr049b])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr015b, htr019c, htr059b])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr016b, htr019c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced129 := (m.htr 1 2 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr129a, htr129b, htr129c, _, _⟩
    linarith only [hlam, htr012c, htr029a, htr129a])
  obtain ⟨htr129a, htr129b, htr129c, _, _⟩ := hforced129
  have hforced123 := (m.htr 1 2 3 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr123a, htr123b, htr123c, _, _⟩
    linarith only [hlam, hc239yx, htr012a, htr019a, htr123a, htr129b])
  obtain ⟨htr123a, htr123b, htr123c, _, _⟩ := hforced123
  have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr139a, htr139b, htr139c, _, _⟩
    linarith only [hlam, htr013c, htr039a, htr139a])
  obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc349yx, htr013a, htr019a, htr134a, htr139b])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc359yx, htr013a, htr019a, htr135a, htr139b])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr014c, htr049a, htr149a])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc459yx, htr014a, htr019a, htr145a, htr149b])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr015c, htr059a, htr159a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc569yx, htr015a, htr019a, htr156a, htr159b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr016c, htr069a, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hc134zy, htr014a, htr019a, htr149b, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc135zy, htr015a, htr019a, htr159b, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc145zy, htr015a, htr019a, htr159b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc156zy, htr016a, htr019a, htr169b, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  rcases m.htr 2 3 4 (by decide) (by decide) with
    ⟨htr234a, htr234b, htr234c, _, _⟩ | ⟨htr234a, htr234b, htr234c, _, _⟩
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13b, hd59a, htr134a, htr234a, htr235a, htr359a])
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
      linarith only [hlam, hd13b, hd59a, htr135a, htr356a, htr456a, htr459a]
    ·
      linarith only [hlam, hd13b, hd69a, htr134a, htr345a, htr456a, htr569a]
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13b, hd49a, htr135a, htr234a, htr235a, htr349a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hd12b, hd59a, htr123a, htr234a, htr345a, htr459a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd12b, hd69a, htr123a, htr235a, htr356a, htr569a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a]
    ·
      linarith only [hlam, hd14b, hd59a, htr145a, htr356a, htr359a, htr456a]

theorem shard_234 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019c : m.d 0 9 < m.d 0 1)
    : False :=
  proof_shard_234 m htr012a htr012b htr012c htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr019a htr019c

#print axioms shard_234
end Jsp404.NoSatElevenDBMTerminal
