import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_048 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
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
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced029 := (m.htr 0 2 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr029a, htr029b, htr029c, _, _⟩
    linarith only [hlam, hc234yx, htr024a, htr029a, htr123a, htr129a])
  obtain ⟨htr029a, htr029b, htr029c, _, _⟩ := hforced029
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr025b, htr029c, htr059b])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr026b, htr029c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr027b, htr029c, htr079b])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
    linarith only [hlam, htr028b, htr029c, htr089b])
  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, htr015c, htr059a, htr125c, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc569yx, htr012c, htr029a, htr125a, htr256a, htr259b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc579yx, htr012c, htr029a, htr125a, htr257a, htr259b])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, htr016c, htr069a, htr126c, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc679yx, htr012c, htr029a, htr126a, htr267a, htr269b])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, htr017c, htr079a, htr127c, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc789yx, htr012c, htr029a, htr127a, htr278a, htr279b])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
    linarith only [hlam, htr018c, htr089a, htr128c, htr289a])
  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc256zy, htr126a, htr129a, htr269b, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hc257zy, htr127a, htr129a, htr279b, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc267zy, htr127a, htr129a, htr279b, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc278zy, htr128a, htr129a, htr289b, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc235zy, htr256c, htr267a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25b, hd69a, htr257a, htr356a, htr357a, htr569a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd23b, hd89a, htr235a, htr357a, htr578a, htr789a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a]
    ·
      linarith only [hlam, hd26b, hd79a, htr267a, htr578a, htr579a, htr678a]
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd23b, hd79a, htr235a, htr356a, htr567a, htr679a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25b, hd79a, htr256a, htr356a, htr357a, htr579a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc235zy, htr257c, htr278a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd25b, hd79a, htr257a, htr578a, htr678a, htr679a]
    ·
      linarith only [hlam, hd25b, hd89a, htr256a, htr567a, htr678a, htr789a]

theorem shard_048 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_048 m htr012c htr015c htr016c htr017c htr018c htr024a htr025b htr026b htr027b htr028b htr123a htr125a htr125c htr126a htr126c htr127a htr127c htr128a htr128c htr129a htr235a

#print axioms shard_048
end Jsp404.NoSatElevenDBMTerminal
