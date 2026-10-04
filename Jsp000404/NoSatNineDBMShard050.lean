import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_050 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr467a : m.d 6 7 + lam ≤ m.d 4 6)
    (htr467b : m.d 6 7 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 4 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 4 6)
    (htr367a : m.d 6 7 + lam ≤ m.d 3 6)
    (htr367b : m.d 6 7 < m.d 3 7)
    (htr367c : m.d 3 7 < m.d 3 6)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr368a : m.d 6 8 + lam ≤ m.d 3 6)
    (htr368b : m.d 6 8 < m.d 3 8)
    (htr368c : m.d 3 8 < m.d 3 6)
    (htr458a : m.d 5 8 + lam ≤ m.d 4 5)
    (htr458b : m.d 5 8 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 4 5)
    (htr468a : m.d 6 8 + lam ≤ m.d 4 6)
    (htr468b : m.d 6 8 < m.d 4 8)
    (htr468c : m.d 4 8 < m.d 4 6)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < (7/2 : ℝ)*lam := by
    linarith only [hd35braw, hp]
  have hd37a := (m.hrange 3 7 (by decide)).1
  have hd38a := (m.hrange 3 8 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, hc123zy, htr013a, htr014a, htr134b, htr234a])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hc123zy, htr023a, htr024a, htr134a, htr234c])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc123zy, htr014c, htr045a, htr134c, htr234a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, htr014b, htr015c, htr045b])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc123zy, htr014c, htr046a, htr134c, htr234a, htr346a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr016a, htr016b, htr016c, _, _⟩
    linarith only [hlam, htr014b, htr016c, htr046b])
  obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hc235xy, htr123c, htr125a, htr134a, htr234a])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc236xy, htr123c, htr126a, htr134a, htr234a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc237xy, htr123c, htr127a, htr134a, htr234a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc238xy, htr123c, htr128a, htr134a, htr234a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc123zy, htr134c, htr145a, htr234a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc123zy, htr134c, htr146a, htr234a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hd01a, hd45b, htr016a, htr167a, htr456a, htr567a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd01a, hd45b, htr016a, htr168a, htr456a, htr568a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  rcases m.htr 3 5 6 (by decide) (by decide) with
    ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
  ·
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr023a, htr025a, htr235c, htr356a, htr456a])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc245yz, htr025a, htr026a, htr236c, htr356c, htr456a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc237xy, hc245yz, htr025a, htr027a, htr234a, htr345b, htr356a, htr456a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hc238xy, hc245yz, htr025a, htr028a, htr234a, htr345b, htr356a, htr456a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr134a, htr135a, htr234a, htr356a, htr456a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc123zy, htr015c, htr056a, htr135c, htr234a, htr345b, htr356a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, htr014b, htr017c, htr047b])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc458yx, htr045b, htr048a, htr056a, htr456a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, htr014b, htr018c, htr048b])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc045yz, htr056b, htr067a, htr456a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr134a, htr136a, htr234a, htr356c, htr456a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr136a, htr137a, htr367c])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr136a, htr138a, htr368c])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr156a, htr234a, htr345b, htr356a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc457yx, htr145b, htr147a, htr156a, htr456a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, hc458yx, htr145b, htr148a, htr156a, htr456a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd37a, hd45b, htr234a, htr237a, htr345b, htr356a, htr456a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, hd38a, hd45b, htr234a, htr238a, htr345b, htr356a, htr456a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr024b, htr047a, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, htr024b, htr048a, htr248a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr235c, htr256a, htr356a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc123zy, hc245yz, htr136a, htr234a, htr256b, htr267a, htr345b, htr356a, htr368a, htr456a, htr678b])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc123zy, hc245yz, htr136a, htr234a, htr256b, htr268a, htr345b, htr356a, htr368a, htr456a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc012xy, hd45b, hd67a, htr015a, htr027a, htr156a, htr278a, htr456a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr134b, htr147a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, htr134b, htr148a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc123zy, htr136a, htr237b, htr278a, htr367c, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr056c, htr067c, htr078a, htr237a, htr378a, htr456a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc123zy, htr136c, htr167c, htr178a, htr237a, htr378a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      linarith only [hlam, hc123zy, hc678yz, htr134b, htr136a, htr147a, htr234a, htr368a, htr478a]
    ·
      linarith only [hlam, hc123zy, hc467zy, htr136a, htr237a, htr367a, htr378a, htr478a]
  ·
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr356a, htr357a, htr567c])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, htr356a, htr358a, htr568c])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      rcases m.htr 3 4 7 (by decide) (by decide) with
        ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
      ·
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc023zy, hc467zy, htr035a, htr234a, htr347a, htr356a, htr567a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc123zy, htr014c, htr047a, htr134c, htr234a, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr014b, htr017c, htr047b])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hc123zy, hc467zy, htr135a, htr234a, htr347a, htr356a, htr567a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc123zy, htr134c, htr147a, htr234a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc467zy, htr014a, htr018a, htr147a, htr168b, htr678b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hd23a, hd45b, htr134a, htr135b, htr156a, htr234a, htr456a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567c])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr156a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr234a, htr237a, htr347b])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc358yx, htr134a, htr135a, htr234a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr234c, htr247a, htr347a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc458yx, htr134a, htr135a, htr234c, htr248a, htr345c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc458yx, htr134a, htr135a, htr345c, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc123zy, htr014c, htr048a, htr134c, htr234a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc123zy, htr134c, htr148a, htr234a, htr348a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        rcases m.htr 0 3 4 (by decide) (by decide) with
          ⟨htr034a, htr034b, htr034c, _, _⟩ | ⟨htr034a, htr034b, htr034c, _, _⟩
        ·
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr034a, htr036a, htr346b])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr034a, htr037a, htr347b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr034a, htr038a, htr348b])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          rcases m.htr 2 5 6 (by decide) (by decide) with
            ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
          ·
            have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr025a, htr025b, htr025c, _, _⟩
              linarith only [hlam, hd23a, hd45b, htr023a, htr025a, htr256a, htr456a])
            obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc245yz, htr025a, htr026a, htr256c, htr456a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hc235yz, hc237xy, htr025a, htr027a, htr134a, htr135a, htr234a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, hc235yz, hc238xy, htr025a, htr028a, htr134a, htr135a, htr234a])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc035xy, hc235yz, htr034a, htr056a, htr134a, htr135a, htr256a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc245yz, htr026b, htr067a, htr256b, htr456a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc245yz, htr026b, htr068a, htr256b, htr456a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr136a, htr136b, htr136c, _, _⟩
              linarith only [hlam, hc235yz, htr135a, htr136a, htr256a, htr356b])
            obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hc023yx, hc367zy, htr026a, htr034a, htr134a, htr137a, htr267a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc035yz, htr057a, htr135a, htr137a, htr357b])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd35b, hd67a, htr037c, htr078a, htr135a, htr137a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hc245yz, htr056a, htr057a, htr257a, htr456a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, hc023yx, hc368zy, htr026a, htr034a, htr134a, htr138a, htr268a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc035yz, htr058a, htr135a, htr138a, htr358b])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, hc245yz, htr056a, htr058a, htr258a, htr456a])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, htr027b, htr078a, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc123zy, htr137c, htr178a, htr234a, htr347b, htr378a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hc012xy, hc678yz, htr014a, htr026a, htr147a, htr268a, htr478a]
            ·
              linarith only [hlam, hc023yx, hc467zy, htr026a, htr034a, htr267a, htr347b, htr378a, htr478a]
          ·
            have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr025a, htr025b, htr025c, _, _⟩
              linarith only [hlam, hc012xy, hc467zy, htr014a, htr025a, htr147a, htr256a, htr567a])
            obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hd12b, hd67a, htr025a, htr026a, htr125a, htr256b, htr567a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc235xy, htr023a, htr025b, htr056a, htr256a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, htr056a, htr057a, htr567c])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr056a, htr058a, htr568c])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr056b, htr067a, htr568a, htr678b])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr056b, htr068a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr136a, htr136b, htr136c, _, _⟩
              linarith only [hlam, hc123zy, htr023a, htr026a, htr136a, htr236c])
            obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hc235xy, hc367zy, htr134a, htr137a, htr234a, htr256a, htr567a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hc123zy, htr023a, htr027a, htr137a, htr237c])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd35b, hd67a, htr037c, htr078a, htr135a, htr137a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, hc235xy, hc368zy, htr134a, htr138a, htr234a, htr256a, htr568a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, hc123zy, htr023a, htr028a, htr138a, htr238c])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, htr256a, htr257a, htr567c])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, htr256a, htr258a, htr568c])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, htr027b, htr078a, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc123zy, htr137c, htr178a, htr234a, htr347b, htr378a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hc235xy, hc678yz, htr234a, htr256a, htr347a, htr478a, htr568a]
            ·
              linarith only [hlam, hc235xy, hc467zy, htr234a, htr256a, htr347b, htr378a, htr478a, htr567a]
        ·
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc235xy, htr023c, htr025a, htr034a, htr234a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc236xy, htr023c, htr026a, htr034a, htr234a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc237xy, htr023c, htr027a, htr034a, htr234a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc238xy, htr023c, htr028a, htr034a, htr234a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hd23a, hd45b, htr034a, htr035b, htr056a, htr234a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567c])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr056a, htr058a, htr568c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, htr056b, htr067a, htr568a, htr678b])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr056b, htr068a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc012xy, hc467zy, htr014a, htr025a, htr147a, htr256a, htr567a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc235yz, htr035a, htr036a, htr256a, htr356b])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc123zy, htr034a, htr036a, htr136a, htr234a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hc015xy, hc457zy, htr014a, htr056a, htr147a, htr256a, htr257a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc235yz, htr035a, htr037a, htr257a, htr357b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc235yz, htr035a, htr038a, htr257a, htr358b, htr578b])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc245yz, htr047c, htr078a, htr257a, htr457c, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc123zy, htr034a, htr037a, htr137a, htr234a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc123zy, htr034a, htr038a, htr138a, htr234a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc245yz, htr146c, htr167c, htr178a, htr257a, htr456c, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr257a, htr258a, htr578b])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc015xy, hc467zy, htr014a, htr056a, htr147a, htr267a, htr268a, htr568a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, htr257c, htr278a, htr578a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd78b, htr034a, htr037a, htr234a, htr378a]
          ·
            linarith only [hlam, hc245yz, htr257a, htr346c, htr367c, htr378a, htr456c, htr578a]
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc137yx, hc457yx, htr014a, htr017a, htr134a, htr145a, htr347a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc138yx, hc457yx, htr014a, htr018a, htr134a, htr145a, htr347a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc123zy, htr024b, htr047a, htr134a, htr234b, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr024c, htr027b, htr047c])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr056a, htr058a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hc457yx, htr134a, htr135a, htr345c, htr347a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc123zy, htr023a, htr025a, htr135a, htr235c])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc123zy, htr023a, htr026a, htr135a, htr236c, htr356c])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc268zy, htr025c, htr028a, htr056a, htr568a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr135a, htr136a, htr356c])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr134a, htr137a, htr347c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr135a, htr138a, htr356c, htr368c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr134b, htr147a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc123zy, hc468zy, htr134b, htr135a, htr148a, htr234a, htr356a, htr568a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc457yx, htr047a, htr048a, htr145a, htr148a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr015c, htr056a, htr156a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, hc457yx, htr234a, htr237a, htr345a, htr347b])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc123zy, hc678yz, htr135a, htr137b, htr178a, htr237a, htr356a, htr568a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc457yx, htr047b, htr078a, htr145a, htr147c, htr178a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc123zy, htr134a, htr234b, htr247a, htr347a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc457yx, htr145a, htr148a, htr247a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc123zy, hc457yx, htr135a, htr234a, htr245b, htr247a, htr256a, htr345a, htr356a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc457yx, htr145a, htr147c, htr178a, htr247b, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr234c, htr248a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc458yx, htr234a, htr238a, htr345a, htr348b])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, htr237c, htr278a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          linarith only [hlam, hc457yx, htr145a, htr147c, htr178a, htr478a]
        ·
          linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a]
    ·
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd03b, hd67a, htr035a, htr356a, htr567c, htr578a, htr678a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd35b, hd67a, htr035a, htr036a, htr356b, htr567c, htr578a, htr678a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd35b, hd67a, htr035a, htr037a, htr357b, htr578a, htr678a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, htr013b, htr017c, htr037b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc367zy, hd23a, hd45b, htr034a, htr037a, htr234a, htr456a, htr567c, htr578a, htr678a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc138yx, htr013b, htr018a, htr034a, htr134a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc367zy, htr037a, htr038a, htr358b, htr578b, htr678a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr045a, htr047a, htr457b, htr578a, htr678a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc467zy, htr047a, htr048a, htr458b, htr578b, htr678a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc056yz, htr067a, htr567c, htr578a, htr678a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr067a, htr068a, htr456a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr135a, htr356a, htr567c, htr578a, htr678a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc035xy, hd35b, hd67a, htr034a, htr056a, htr134a, htr135a, htr567c, htr578a, htr678a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr056a, htr057a, htr456a, htr578a, htr678a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr056a, htr058a, htr456a, htr578b, htr678a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc045yz, htr057b, htr078a, htr456a, htr567c, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hd35b, hd67a, htr135a, htr136a, htr356b, htr567c, htr578a, htr678a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      rcases m.htr 1 3 7 (by decide) (by decide) with
        ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
      ·
        linarith only [hlam, hc367zy, hd23a, hd45b, htr134a, htr137a, htr234a, htr456a, htr567c, htr578a, htr678a]
      ·
        linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr357b, htr578a, htr678a]

theorem shard_050 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr467a : m.d 6 7 + lam ≤ m.d 4 6)
    (htr467b : m.d 6 7 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 4 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 4 6)
    (htr367a : m.d 6 7 + lam ≤ m.d 3 6)
    (htr367b : m.d 6 7 < m.d 3 7)
    (htr367c : m.d 3 7 < m.d 3 6)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr368a : m.d 6 8 + lam ≤ m.d 3 6)
    (htr368b : m.d 6 8 < m.d 3 8)
    (htr368c : m.d 3 8 < m.d 3 6)
    (htr458a : m.d 5 8 + lam ≤ m.d 4 5)
    (htr458b : m.d 5 8 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 4 5)
    (htr468a : m.d 6 8 + lam ≤ m.d 4 6)
    (htr468b : m.d 6 8 < m.d 4 8)
    (htr468c : m.d 4 8 < m.d 4 6)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    : False :=
  proof_shard_050 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr346a htr346b htr346c htr236a htr236b htr236c htr246a htr246b htr246c htr367a htr367b htr367c htr568a htr568b htr568c htr368a htr368b htr368c htr458a htr458b htr458c htr468a htr468b htr468c htr023a htr023b htr023c htr134a htr134b htr134c

#print axioms shard_050
end Jsp404.NoSatNineDBMTerminal
