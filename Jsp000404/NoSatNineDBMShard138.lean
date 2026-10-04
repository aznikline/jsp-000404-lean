import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_138 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < (7/2 : ℝ)*lam := by
    linarith only [hd06braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < (7/2 : ℝ)*lam := by
    linarith only [hd24braw, hp]
  have hd28a := (m.hrange 2 8 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < (7/2 : ℝ)*lam := by
    linarith only [hd35braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < (7/2 : ℝ)*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, htr123a, htr125a, htr235b])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc267yz, hc345zy, htr123a, htr127a, htr235a, htr456a, htr567a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, htr123c, htr135a, htr235a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc126xy, hc345zy, htr123a, htr167a, htr235a, htr456a, htr567a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd12a, hd67b, htr123a, htr235a, htr356a, htr567a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc034yz, htr045a, htr345c, htr356a, htr456a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc345zy, htr045a, htr046a, htr356a, htr456c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc345zy, htr123c, htr136a, htr235a, htr356b, htr456a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, htr123b, htr126c, htr136b])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, htr136b, htr137c, htr167b])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc134yz, htr145a, htr345c, htr356a, htr456a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc345zy, htr145a, htr146a, htr356a, htr456c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc345zy, htr235a, htr236a, htr356b, htr456a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr124c, htr146a, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc345zy, htr236c, htr267a, htr356c, htr456a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr236b, htr237c, htr267b])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457xy, htr345c, htr347a, htr356a, htr456a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458xy, htr345c, htr348a, htr356a, htr456a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc345zy, htr356c, htr367a, htr456a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hd06b, hd12a, htr067a, htr123a, htr236a, htr367a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hd28a, hd67b, htr123a, htr128a, htr236a, htr367a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hd12a, hd67b, htr123a, htr237a, htr378a, htr678a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc124xy, hc678yx, htr123a, htr146a, htr236a, htr367a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, htr456b, htr458c, htr468b])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc345zy, htr356a, htr456b, htr468a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hd45a, hd67b, htr067a, htr068a, htr456a, htr568a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd45a, hd67b, htr167a, htr168a, htr456a, htr568a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr136b, htr138c, htr168b])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hd13a, hd67b, htr138a, htr236a, htr238a, htr367a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hc345zy, htr236c, htr268a, htr356c, htr456a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hc345zy, htr356c, htr368a, htr456a, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  rcases m.htr 0 2 3 (by decide) (by decide) with
    ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
  ·
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, htr023a, htr024a, htr234b])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, htr023a, htr025a, htr235b])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr023a, htr026a, htr236b])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, htr023a, htr027a, htr236b, htr267b])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr023a, htr028a, htr238b])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr023c, htr034a, htr235a, htr345c])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr023c, htr035a, htr236a, htr356c])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr023c, htr036a, htr236a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr045a, htr047a, htr457c, htr578a, htr678a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc467yz, htr047a, htr048a, htr458c, htr578c, htr678a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc027xy, hc345zy, htr023a, htr078a, htr235a, htr456a, htr567b, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr145a, htr147a, htr457c, htr578a, htr678a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hc012yx, hc467yz, htr014a, htr023a, htr147a, htr236a, htr367a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc124xy, hc167yz, htr014a, htr017a, htr123a, htr236a, htr367a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc124xy, hc168yz, htr014a, htr018a, htr123a, htr236a, htr368a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr157c, htr578a, htr678a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, htr015a, htr017a, htr157c])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr012a, htr015b, htr056a, htr567b, htr578a, htr678a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr056a, htr057a, htr456a, htr578a, htr678a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr056a, htr058a, htr456a, htr578c, htr678a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr156a, htr157a, htr567b])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr016a, htr017b, htr078a, htr156b, htr456a, htr678a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015c, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 1 7 8 (by decide) (by decide) with
        ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
      ·
        linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a]
      ·
        linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc025xy, hc678zy, htr023a, htr057a, htr236a, htr368a, htr578a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc125xy, hc678zy, htr123a, htr157a, htr236a, htr368a, htr578a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc124xy, hc167yz, htr014a, htr017a, htr123a, htr236a, htr367a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc124xy, hc168yz, htr014a, htr018a, htr123a, htr236a, htr368a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hd12a, hd34b, htr012a, htr014a, htr147a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc124xy, htr012a, htr014b, htr047a, htr147a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc467yz, hd12a, hd34b, htr047a, htr048a, htr123a, htr236a, htr348a, htr367a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr014c, htr048a, htr148a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr124c, htr147a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024c, htr048a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr127c, htr178a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          linarith only [hlam, hc127xy, hc467yz, htr123a, htr178a, htr236a, htr367a, htr478a]
        ·
          linarith only [hlam, hc124xy, hc678zy, htr123a, htr147a, htr236a, htr368a, htr478a]
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, htr014a, htr015a, htr145c])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr014a, htr016a, htr146c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc127xy, hc345zy, htr014a, htr017a, htr123a, htr145a, htr235a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc128xy, hc345zy, htr014a, htr018a, htr123a, htr145a, htr235a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc012yx, hc467yz, htr014a, htr023a, htr147a, htr236a, htr367a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc024xy, hc345zy, htr023a, htr047a, htr145a, htr147a, htr235a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc468yz, hd12a, hd34b, htr047a, htr048a, htr123a, htr236a, htr347a, htr368a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc457xy, htr045c, htr047a, htr056a, htr456a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr014b, htr048a, htr148a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr015b, htr056a, htr156a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc012yx, hc678zy, htr017a, htr023a, htr178a, htr236a, htr368a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc457xy, htr047c, htr078a, htr145a, htr147b, htr178a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc012yx, hc345zy, htr014a, htr023a, htr145a, htr235b, htr256a, htr356a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc457xy, htr245c, htr247a, htr256a, htr456a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc458xy, htr145a, htr147a, htr247a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc245zy, htr145a, htr147b, htr178a, htr257a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc245zy, htr045a, htr048a, htr258a, htr458c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr145a, htr147a, htr247b, htr278a, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc345zy, htr145a, htr147b, htr178a, htr357a, htr578a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc345zy, htr256a, htr258a, htr358a, htr456a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          linarith only [hlam, hd45a, hd67b, htr145a, htr147a, htr478a, htr678a]
        ·
          linarith only [hlam, hc457xy, htr145a, htr147b, htr178a, htr478a]
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc124xy, htr012c, htr014a, htr023a, htr123a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, htr014a, htr015a, htr145c])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, htr014a, htr016a, htr146c])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc127xy, htr012c, htr017a, htr023a, htr123a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc128xy, htr012c, htr018a, htr023a, htr123a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr023a, htr026a, htr123a, htr267a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc012zy, htr023c, htr034a, htr123a, htr234a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hc012zy, htr023c, htr035a, htr123a, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc012zy, htr023c, htr036a, htr123a, htr236a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr036a, htr037a, htr367b])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr036a, htr038a, htr368b])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc245zy, hd12a, hd67b, htr023a, htr025a, htr123a, htr456a, htr567b, htr578a, htr678a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr045a, htr047a, htr457c, htr578a, htr678a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc467yz, htr047a, htr048a, htr458c, htr578c, htr678a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr023b, htr035b, htr056a, htr123a, htr567b, htr578a, htr678a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr056a, htr057a, htr456a, htr578a, htr678a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr025c, htr027b, htr057c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr056a, htr058a, htr456a, htr578c, htr678a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr025c, htr028b, htr058c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc045zy, htr057c, htr078a, htr456a, htr567b, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr145a, htr147a, htr457c, htr578a, htr678a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc012zy, hc467yz, htr024a, htr123a, htr124c, htr147a, htr236a, htr367a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc045zy, hc467yz, htr058a, htr147a, htr148a, htr456a, htr458c, htr567b, htr578a, htr678a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hd24b, hd45a, htr024a, htr025a, htr125c, htr156a, htr456a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr156a, htr157a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr156a, htr158a, htr568b])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr017b, htr078a, htr178a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      rcases m.htr 2 5 6 (by decide) (by decide) with
        ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
      ·
        linarith only [hlam, hd12a, hd67b, htr123a, htr235b, htr256a, htr567b, htr578a, htr678a]
      ·
        linarith only [hlam, hd24b, hd45a, htr024a, htr025a, htr256a, htr456a]
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc125xy, hc678zy, htr123a, htr157a, htr236a, htr368a, htr578a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      rcases m.htr 0 2 4 (by decide) (by decide) with
        ⟨htr024a, htr024b, htr024c, _, _⟩ | ⟨htr024a, htr024b, htr024c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hd12a, hd34b, htr023a, htr024b, htr047a, htr123a, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hd12a, hd34b, htr023a, htr024b, htr048a, htr123a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr024c, htr047a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024c, htr048a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        rcases m.htr 3 5 7 (by decide) (by decide) with
          ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
        ·
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hd12a, hd57b, htr023a, htr025a, htr123a, htr235c, htr357a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hd12a, hd57b, htr023b, htr035b, htr056a, htr123a, htr356a, htr357a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr035c, htr057a, htr357a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr056a, htr057b, htr078a, htr456a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hd24b, hd45a, htr024a, htr025a, htr125c, htr156a, htr456a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr156a, htr158a, htr568b])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          rcases m.htr 2 5 6 (by decide) (by decide) with
            ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd57b, htr123a, htr235b, htr256a, htr356a, htr357a]
          ·
            linarith only [hlam, hd24b, hd45a, htr024a, htr025a, htr256a, htr456a]
        ·
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc345zy, htr046b, htr067b, htr078a, htr357a, htr456b, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc345zy, htr145a, htr147a, htr357a, htr457c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc345zy, htr145a, htr148a, htr357a, htr458c, htr578c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc345zy, htr156a, htr157a, htr357a, htr456a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr156a, htr158a, htr568b])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc345zy, htr146b, htr167b, htr178a, htr357a, htr456b, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc012zy, hc678zy, htr027a, htr123a, htr127c, htr178a, htr236a, htr368a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc345zy, htr026a, htr027a, htr237c, htr256b, htr357c, htr456a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, htr025a, htr026a, htr256b])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc345zy, htr025c, htr027a, htr056a, htr237c, htr357c, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr056a, htr058a, htr568b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          rcases m.htr 2 5 7 (by decide) (by decide) with
            ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd35b, htr023a, htr027a, htr123a, htr257c, htr357a]
          ·
            linarith only [hlam, htr256a, htr257a, htr567b]
      ·
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, htr024a, htr025a, htr245c])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc012zy, hc345zy, htr023b, htr024a, htr035b, htr056a, htr123a, htr245a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc457xy, htr045c, htr047a, htr056a, htr456a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr024c, htr027b, htr047c])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc458xy, htr045c, htr048a, htr056a, htr456a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr024c, htr028b, htr048c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc012zy, hc678zy, htr024c, htr045c, htr057a, htr123a, htr236a, htr368a, htr578a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr056a, htr057b, htr078a, htr456a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        rcases m.htr 1 4 7 (by decide) (by decide) with
          ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
        ·
          linarith only [hlam, hc012zy, hc345zy, htr024c, htr047a, htr123a, htr145a, htr147a, htr235a]
        ·
          linarith only [hlam, hc012zy, hc467yz, htr024a, htr123a, htr124c, htr147a, htr236a, htr367a]

theorem shard_138 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False :=
  proof_shard_138 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr245a htr245b htr245c htr346a htr346b htr346c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c htr235a htr235b htr235c

#print axioms shard_138
end Jsp404.NoSatNineDBMTerminal
