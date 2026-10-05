import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_244 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019c : m.d 0 9 < m.d 0 1)
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
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr015b, htr019c, htr059b])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr016b, htr019c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr017b, htr019c, htr079b])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
    linarith only [hlam, htr018b, htr019c, htr089b])
  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
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
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc679yx, htr016a, htr019a, htr167a, htr169b])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc689yx, htr016a, htr019a, htr168a, htr169b])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, htr017c, htr079a, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
    linarith only [hlam, htr018c, htr089a, htr189a])
  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hc126zy, htr016a, htr019a, htr169b, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc135zy, htr015a, htr019a, htr159b, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hc136zy, htr016a, htr019a, htr169b, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc156zy, htr016a, htr019a, htr169b, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc167zy, htr017a, htr019a, htr179b, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
    linarith only [hlam, hc168zy, htr018a, htr019a, htr189b, htr689a])
  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd12b, hd69a, htr126a, htr267a, htr567a, htr569a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd16b, hd89a, htr167a, htr267a, htr268a, htr689a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc135zy, htr156c, htr167a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd12b, hd69a, htr123a, htr235a, htr356a, htr569a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13b, hd69a, htr135a, htr235a, htr236a, htr369a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 8 (by decide) (by decide) with
      ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
    ·
      linarith only [hlam, hc123zy, htr136c, htr168a, htr236a, htr368a]
    ·
      linarith only [hlam, hd13b, hd69a, htr136a, htr268a, htr269a, htr368a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd15b, hd69a, htr156a, htr267a, htr269a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd16b, hd79a, htr168a, htr267a, htr268a, htr679a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr135a, htr356a, htr567a, htr679a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr156a, htr235a, htr356a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13b, hd59a, htr136a, htr235a, htr236a, htr359a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 8 (by decide) (by decide) with
      ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
    ·
      linarith only [hlam, hd12b, hd69a, htr126a, htr268a, htr368a, htr369a]
    ·
      linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a]

theorem shard_244 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    : False :=
  proof_shard_244 m htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr019c htr123a htr126a htr135a htr135c htr136a htr136c

#print axioms shard_244
end Jsp404.NoSatElevenDBMTerminal
