import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_595 {lam p : ℝ} (m : ElevenModel lam p)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr123c, htr128b, htr138c])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, htr124c, htr128b, htr148c])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr125c, htr128b, htr158c])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr126c, htr128b, htr168c])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr127c, htr128b, htr178c])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr123b, htr138a, htr238a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hc348xy, htr123a, htr128a, htr234a, htr238c])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, htr124b, htr148a, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc458xy, htr124a, htr128a, htr245a, htr248c])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc468xy, htr124a, htr128a, htr246a, htr248c])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr125b, htr158a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc568xy, htr125a, htr128a, htr256a, htr258c])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr126b, htr168a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc678xy, htr126a, htr128a, htr267a, htr268c])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr127b, htr178a, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc245yz, htr125a, htr128a, htr258c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc246yz, htr126a, htr128a, htr268c, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc256yz, htr126a, htr128a, htr268c, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc267yz, htr127a, htr128a, htr278c, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 3 4 5 (by decide) (by decide) with
    ⟨htr345a, htr345b, htr345c, _, _⟩ | ⟨htr345a, htr345b, htr345c, _, _⟩
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd24a, hd58b, htr246a, htr345a, htr346a, htr458a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr234a, htr345a, htr456a, htr568a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd25a, hd68b, htr256a, htr467a, htr468a, htr567a]
    ·
      linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a]
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd24a, hd68b, htr245a, htr345a, htr346a, htr468a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd24a, hd78b, htr245a, htr456a, htr567a, htr678a]
    ·
      linarith only [hlam, hd24a, hd68b, htr246a, htr467a, htr567a, htr568a]

theorem shard_595 {lam p : ℝ} (m : ElevenModel lam p)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    : False :=
  proof_shard_595 m htr123a htr123b htr123c htr124a htr124b htr124c htr125a htr125b htr125c htr126a htr126b htr126c htr127a htr127b htr127c htr128a htr128b

#print axioms shard_595
end Jsp404.NoSatElevenDBMTerminal
