import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_222 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < (7/2 : ℝ)*lam := by
    linarith only [hd14braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < (7/2 : ℝ)*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < (7/2 : ℝ)*lam := by
    linarith only [hd38braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < (7/2 : ℝ)*lam := by
    linarith only [hd57braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced124 := (m.htr 1 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr124a, htr124b, htr124c, _, _⟩
    linarith only [hlam, hc234yx, htr012a, htr013a, htr123c, htr124a])
  obtain ⟨htr124a, htr124b, htr124c, _, _⟩ := hforced124
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hc123xy, htr012c, htr013a, htr024a, htr124a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hc235yx, htr012a, htr013a, htr123c, htr125a])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hc123xy, htr012c, htr013a, htr025a, htr125a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc236yx, htr012a, htr013a, htr123c, htr126a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hc123xy, htr012c, htr013a, htr026a, htr126a])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc237yx, htr012a, htr013a, htr123c, htr127a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc123xy, htr012c, htr013a, htr027a, htr127a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc238yx, htr012a, htr013a, htr123c, htr128a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc123xy, htr012c, htr013a, htr028a, htr128a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr134a, htr234a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hc123xy, htr012a, htr013b, htr034a, htr134a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr034a, htr035a, htr345c])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr034b, htr045a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, htr134a, htr135a, htr345c])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, htr134b, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc456xy, htr034a, htr036a, htr345a, htr346c])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc045zy, htr056a, htr345a, htr346a, htr456c])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013c, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, htr013c, htr036a, htr123c, htr236a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc245zy, htr256a, htr345a, htr346a, htr456c])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567yx, htr345a, htr346a, htr456c, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc456xy, htr345c, htr346a, htr357a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568yx, htr345a, htr346a, htr456c, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc456xy, htr345c, htr346a, htr358a, htr458a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456xy, htr036b, htr067a, htr345a, htr346b, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr036c, htr037b, htr067c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr123c, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr026c, htr067a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc123xy, hc678xy, htr013c, htr036a, htr125a, htr256a, htr367a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc456xy, htr036b, htr068a, htr345a, htr346b, htr468a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr036c, htr038b, htr068c])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr013c, htr038a, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr026c, htr068a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc123xy, hc678yz, htr013c, htr036a, htr124a, htr247a, htr368a, htr457c, htr578a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc123xy, hc678yz, htr013c, htr036a, htr125a, htr257a, htr368a, htr578a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc245zy, htr034b, htr047a, htr257a, htr345a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc567yx, htr027c, htr078a, htr256a, htr257c, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc245zy, htr134b, htr147a, htr257a, htr345a, htr457c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc567yx, htr127c, htr178a, htr256a, htr257c, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc123xy, hc678yz, htr012a, htr013c, htr017a, htr036a, htr178a, htr368a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hc456xy, htr245c, htr246a, htr257a, htr457a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr246a, htr248a, htr468c])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc567yx, htr256a, htr257c, htr278a, htr578a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr127a, htr168a, htr278a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc245zy, htr257a, htr345a, htr347a, htr457c])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr137b, htr278a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr147b, htr278a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
      ·
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc456xy, htr014a, htr017a, htr137b, htr146a, htr345b, htr357b])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc124xy, hc145zy, htr012a, htr015a, htr146a, htr345a, htr346a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc124xy, htr012a, htr014b, htr046a, htr146a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr046a, htr048a, htr468c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc124xy, hc245zy, htr012b, htr025b, htr057a, htr146a, htr257a, htr345a, htr346a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr146a, htr148a, htr468c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        rcases m.htr 1 5 7 (by decide) (by decide) with
          ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
        ·
          linarith only [hlam, hc135yx, htr013a, htr015c, htr057a, htr157a]
        ·
          linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr157a, htr457a]
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, htr014a, htr015a, htr145c])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd13b, hd45a, htr013a, htr014c, htr046a, htr345a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        rcases m.htr 0 5 7 (by decide) (by decide) with
          ⟨htr057a, htr057b, htr057c, _, _⟩ | ⟨htr057a, htr057b, htr057c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc245zy, htr012b, htr013a, htr014a, htr025b, htr057a, htr134b, htr257a, htr345a]
        ·
          linarith only [hlam, hc456xy, htr045c, htr046a, htr057a, htr457a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd56b, hd67a, htr056a, htr057a, htr578a, htr678a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567zy, htr057a, htr058a, htr578b, htr678a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd56b, hd67a, htr156a, htr157a, htr578a, htr678a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc123xy, hc567zy, htr012a, htr013c, htr015a, htr036a, htr157a, htr367a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015b, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hd56b, hd67a, htr256a, htr257a, htr578a, htr678a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc123xy, hc567zy, htr013a, htr016a, htr125a, htr167a, htr257a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc567zy, htr257a, htr258a, htr578b, htr678a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc123xy, hc567zy, htr013c, htr036a, htr127a, htr278a, htr367a, htr578a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc123xy, hc567zy, htr013c, htr037a, htr125a, htr257a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
      ·
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc456xy, htr014a, htr015a, htr135b, htr146a, htr345b])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc124xy, htr012a, htr014b, htr046a, htr146a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr046a, htr047a, htr467c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr046a, htr048a, htr468c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr146a, htr147a, htr467c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr146a, htr148a, htr468c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr124c, htr146a, htr246a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc124xy, hc457yz, htr125a, htr146a, htr257a, htr346a, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hd13b, hd45a, htr013a, htr017a, htr147b, htr345a, htr347a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hd45a, hd57b, htr047b, htr078a, htr345a, htr347a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr017c, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hd13b, hd45a, htr013a, htr018a, htr178b, htr345a, htr347b, htr378a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc567zy, htr347b, htr348a, htr378a, htr468b, htr578a, htr678b])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a]
        ·
          linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a]
      ·
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd13b, hd45a, htr013a, htr014c, htr046a, htr345a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        rcases m.htr 1 4 6 (by decide) (by decide) with
          ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
        ·
          linarith only [hlam, hc456xy, htr014a, htr016a, htr134b, htr146c, htr345a]
        ·
          linarith only [hlam, htr014b, htr046a, htr146a]
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr034a, htr036a, htr346c])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr034b, htr046a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013c, htr034a, htr136a, htr346c])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134b, htr146a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, htr123c, htr134a, htr236a, htr346c])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr234b, htr246a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc123xy, hc456yz, htr126a, htr134a, htr267a, htr346a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, htr236c, htr237b, htr267c])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr034a, htr037a, htr237a, htr345a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr246c, htr247b, htr267c])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc067zy, htr078a, htr567a, htr568a, htr678c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc167zy, htr178a, htr567a, htr568a, htr678c])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc267zy, htr278a, htr567a, htr568a, htr678c])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd23b, hd45a, htr234a, htr346c, htr368a, htr456a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, htr037b, htr078a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr457a, htr458a, htr567c, htr568b])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr456c, htr468a, htr568a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, htr457c, htr478a, htr567c, htr568a, htr678c])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        rcases m.htr 3 5 6 (by decide) (by decide) with
          ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
        ·
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc678xy, htr356a, htr357a, htr567b, htr568a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr356a, htr358a, htr568b])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 4 6 7 (by decide) (by decide) with
            ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
          ·
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc456yz, htr034b, htr047a, htr346a, htr467c, htr567a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr567a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc678xy, htr056a, htr057a, htr567b, htr568a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr056a, htr058a, htr568b])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr056c, htr068a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hc456yz, htr134b, htr147a, htr346a, htr467c, htr567a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hd12a, hd68b, htr012a, htr015a, htr156a, htr568a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, hc358xy, htr013a, htr015a, htr135b, htr138a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, htr015b, htr057a, htr157a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr156a, htr158a, htr568b])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr156c, htr168a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr238a, htr238b, htr238c, _, _⟩
              linarith only [hlam, htr123c, htr138a, htr238a])
            obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, hc468xy, htr246c, htr248a, htr267a, htr467a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr567a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hc123xy, hc456yz, htr013a, htr014a, htr125a, htr134b, htr256a, htr346a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc123xy, hc168yz, htr013a, htr018a, htr125a, htr256a, htr568a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hc458xy, htr014a, htr015a, htr135b, htr148a, htr345b])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc124xy, htr012a, htr014b, htr048a, htr148a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hc678xy, htr256a, htr257a, htr567b, htr568a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, htr256a, htr258a, htr568b])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr256c, htr268a, htr568a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr347a, htr347b, htr347c, _, _⟩
              linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
            obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
            rcases m.htr 3 4 8 (by decide) (by decide) with
              ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
            ·
              linarith only [hlam, hc124xy, hc456yz, htr125a, htr148a, htr256a, htr346a, htr348a]
            ·
              linarith only [hlam, hc123xy, hc468yz, htr125a, htr134a, htr256a, htr348a, htr568a]
          ·
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr013a, htr014a, htr134b, htr346a, htr467a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr134a, htr346a, htr467a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hc678xy, htr034a, htr038a, htr346a, htr368c, htr467a])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr034b, htr047a, htr346a, htr467c])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc678xy, htr034b, htr048a, htr346a, htr458c, htr467a, htr568c])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc123xy, hc678xy, htr012b, htr025b, htr056a, htr134a, htr346a, htr467a, htr568a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, htr056a, htr057a, htr567c])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc678xy, htr056a, htr058a, htr567a, htr568c])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr036b, htr067a, htr346b, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc045zy, htr056c, htr068a, htr456a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc123xy, hc678xy, htr012a, htr016b, htr068a, htr134a, htr346a, htr467a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc145zy, hc678xy, htr015a, htr016a, htr136b, htr346b, htr456a, htr467a, htr568a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, htr015c, htr018b, htr058c])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, htr014a, htr015c, htr058a, htr134c, htr138a, htr358c])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, htr014a, htr016a, htr136b, htr147a, htr346b, htr467c])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr014a, htr015c, htr058a, htr148a, htr458c])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            rcases m.htr 1 5 6 (by decide) (by decide) with
              ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
            ·
              linarith only [hlam, hc135yx, htr013a, htr015c, htr058a, htr156a, htr568b]
            ·
              linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr156a, htr456a]
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hd13b, hd45a, htr013a, htr014a, htr134b, htr345c, htr356a, htr456a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          rcases m.htr 0 1 5 (by decide) (by decide) with
            ⟨htr015a, htr015b, htr015c, _, _⟩ | ⟨htr015a, htr015b, htr015c, _, _⟩
          ·
            linarith only [hlam, hc123xy, hc145zy, htr012a, htr015a, htr134a, htr345c, htr356a, htr456a]
          ·
            linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr135b, htr356a, htr456a]
      ·
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc123xy, hc456yz, htr126a, htr134a, htr268a, htr346a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr236c, htr238b, htr268c])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hd23b, hd45a, htr034a, htr038a, htr238a, htr345a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr138a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr246c, htr248b, htr268c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        rcases m.htr 3 5 6 (by decide) (by decide) with
          ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
        ·
          rcases m.htr 4 6 7 (by decide) (by decide) with
            ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
          ·
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc456yz, htr034b, htr047a, htr346a, htr467c, htr567a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr568a, htr678b])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc456yz, htr056a, htr058a, htr467a, htr568b, htr678b])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc246zy, htr027c, htr078a, htr267c, htr467a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hc456yz, htr134b, htr147a, htr346a, htr467c, htr567a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr568a, htr678b])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc123xy, hc456yz, htr012a, htr015a, htr134a, htr156a, htr346a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, htr015b, htr057a, htr157a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr015b, htr058a, htr158a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc246zy, htr127c, htr178a, htr267c, htr467a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr568a, htr678b])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hc123xy, hc456yz, htr013a, htr014a, htr125a, htr134b, htr256a, htr346a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hd12a, hd24b, htr012a, htr014a, htr148a, htr248a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc124xy, htr012a, htr014b, htr048a, htr148a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hc456yz, htr256a, htr257a, htr467a, htr567b])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, hc456yz, htr256a, htr258a, htr467a, htr568b, htr678b])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc246zy, htr267c, htr278a, htr467a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr347a, htr347b, htr347c, _, _⟩
              linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
            obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
            have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr348a, htr348b, htr348c, _, _⟩
              linarith only [hlam, hc124xy, hc456yz, htr125a, htr148a, htr256a, htr346a, htr348a])
            obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc123xy, hc478yz, htr012a, htr017a, htr134a, htr178a, htr348a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc123xy, hc456yz, htr013a, htr017a, htr125a, htr167b, htr256a, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, htr016a, htr017a, htr167b])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr067a, htr068a, htr678b])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr167a, htr168a, htr678b])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc456yz, htr017a, htr018a, htr147b, htr168c, htr467b, htr568a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hc123xy, htr013a, htr015a, htr125a, htr135b, htr257a, htr357a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, hc123xy, htr013a, htr015a, htr125a, htr135b, htr258a, htr358a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, htr136b, htr167a, htr367a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, htr136b, htr167a, htr368a, htr678b])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr137b, htr278a, htr378a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr458a, htr458b, htr458c, _, _⟩
              linarith only [hlam, hc123xy, htr125a, htr134a, htr258a, htr345a, htr458a])
            obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, htr467a, htr468a, htr678b])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc123xy, htr127a, htr134a, htr278a, htr347a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              linarith only [hlam, hc123xy, hc478yz, htr125a, htr134a, htr257a, htr348a, htr578a]
            ·
              linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a]
          ·
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr013a, htr014a, htr134b, htr346a, htr467a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr134a, htr346a, htr467a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr034b, htr047a, htr346a, htr467c])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hd24b, hd67a, htr034b, htr048a, htr248a, htr346a, htr467a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr036b, htr067a, htr346b, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hc123xy, htr012a, htr014a, htr134a, htr147a, htr346a, htr467c])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr014c, htr048a, htr148a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr136b, htr167a, htr346b, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hc123xy, hc567zy, htr125a, htr134a, htr257a, htr346a, htr467a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc137yx, hc267zy, htr134a, htr178a, htr278a, htr346a, htr467a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr347a, htr347b, htr347c, _, _⟩
              linarith only [hlam, htr346a, htr347a, htr467c])
            obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
            have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr348a, htr348b, htr348c, _, _⟩
              linarith only [hlam, hd24b, hd67a, htr248a, htr346a, htr348a, htr467a])
            obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, htr346b, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr137b, htr278a, htr378a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr458a, htr458b, htr458c, _, _⟩
              linarith only [hlam, hc578yz, htr257b, htr278a, htr457a, htr458a])
            obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc123xy, hc678yz, htr127a, htr134a, htr278a, htr346a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc045zy, htr056a, htr456b, htr468a, htr568a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc456yz, htr056a, htr058a, htr468a, htr568b])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc145zy, htr156a, htr456b, htr468a, htr568a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc123xy, hc456yz, htr012a, htr015a, htr134a, htr156a, htr346a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr157a, htr457a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc135yx, htr013a, htr015c, htr057a, htr157a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr015b, htr058a, htr158a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            rcases m.htr 2 5 6 (by decide) (by decide) with
              ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
            ·
              linarith only [hlam, hc135yx, hc456yz, htr134a, htr157a, htr256a, htr257a, htr346a]
            ·
              linarith only [hlam, hc245zy, htr256a, htr456b, htr468a, htr568a]
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hd13b, hd45a, htr013a, htr014a, htr134b, htr345c, htr356a, htr456a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          rcases m.htr 0 1 5 (by decide) (by decide) with
            ⟨htr015a, htr015b, htr015c, _, _⟩ | ⟨htr015a, htr015b, htr015c, _, _⟩
          ·
            linarith only [hlam, hc123xy, hc145zy, htr012a, htr015a, htr134a, htr345c, htr356a, htr456a]
          ·
            linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr135b, htr356a, htr456a]
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd13b, hd57a, htr013a, htr014a, htr134b, htr345a, htr457a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc123xy, hc157zy, htr012a, htr017a, htr134a, htr345a, htr457a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hd38b, hd57a, htr034a, htr038a, htr346a, htr456b, htr457a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr034b, htr047a, htr345a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr035b, htr057a, htr345b, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr036b, htr067a, htr346b, htr456b, htr457a, htr567b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr014a, htr134a, htr147a, htr345a, htr457c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc478xy, htr014a, htr017a, htr147b, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd14b, hd57a, htr034b, htr048a, htr148a, htr345a, htr457a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr135b, htr157a, htr345b, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr136b, htr167a, htr346b, htr456b, htr457a, htr567b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124c, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc123xy, hc567yx, htr125a, htr134a, htr256a, htr345a, htr457a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc578xy, htr256a, htr258a, htr456a, htr457a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc678xy, htr256b, htr268a, htr456a, htr457a, htr567b])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc137yx, hc257zy, htr134a, htr178a, htr278a, htr345a, htr457a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr346a, htr347a, htr456b, htr457c])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd14b, hd57a, htr148a, htr346a, htr348a, htr456b, htr457a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr234a, htr345c, htr356a, htr456a, htr457a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr345b, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr137b, htr278a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc123xy, hc578yz, htr127a, htr134a, htr278a, htr345a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc567yx, htr356a, htr358a, htr457a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc123xy, hc678yz, htr127a, htr134a, htr278a, htr346a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr234a, htr346c, htr368a, htr456b, htr457a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        linarith only [hlam, hc678xy, htr456a, htr457a, htr567b, htr568a]
      ·
        linarith only [hlam, hc567yx, htr456b, htr457a, htr468a, htr568a]

theorem shard_222 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    : False :=
  proof_shard_222 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c

#print axioms shard_222
end Jsp404.NoSatNineDBMTerminal
