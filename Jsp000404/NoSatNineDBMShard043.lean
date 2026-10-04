import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_043 {lam p : ℝ} (m : NineModel lam p)
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
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
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
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  have hd03a := (m.hrange 0 3 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd18a := (m.hrange 1 8 (by decide)).1
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd28a := (m.hrange 2 8 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < (7/2 : ℝ)*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < (7/2 : ℝ)*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, hc067yz, htr078a, htr567a, htr568a, htr678b])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc167yz, htr178a, htr567a, htr568a, htr678b])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc267yz, htr278a, htr567a, htr568a, htr678b])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd23a, hd45b, htr234a, htr346b, htr368a, htr456a, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hc367yz, htr378a, htr567a, htr568a, htr678b])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hd45b, hd78a, htr234a, htr237a, htr345a, htr378a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, htr457a, htr458a, htr567b, htr568c])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, htr456b, htr468a, htr568a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, htr457b, htr478a, htr567b, htr568a, htr678b])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  rcases m.htr 0 2 3 (by decide) (by decide) with
    ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, htr012b, htr014a, htr023a, htr124b, htr234b])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc145yz, htr012b, htr015a, htr023a, htr234a, htr345a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc146yz, htr012b, htr016a, htr023a, htr234a, htr346a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hd45b, hd78a, htr012b, htr017a, htr023a, htr178a, htr234a, htr345a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc128yx, htr012b, htr018a, htr023a, htr123a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
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
      linarith only [hlam, htr023a, htr027a, htr237b])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hd28a, hd45b, htr023a, htr028a, htr234a, htr345a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr023c, htr034a, htr234a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr023c, htr035a, htr234a, htr345b])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr023c, htr036a, htr234a, htr346b])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr023c, htr037a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr024c, htr045a, htr124a, htr234a, htr346a, htr456c])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr024c, htr046a, htr124a, htr234a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc012yz, hc457yx, htr023a, htr024c, htr047a, htr124a, htr234a, htr345a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc012yz, hc458yx, htr023a, htr024c, htr048a, htr124a, htr234a, htr345a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr034b, htr038c, htr048b])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc026xy, hc456zy, htr023a, htr067a, htr234a, htr346a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc046yz, hd02a, hd45b, htr023a, htr068a, htr234a, htr346a, htr456a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr134a, htr234a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, htr134a, htr135a, htr345b])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr134a, htr136a, htr346b])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr023a, htr134a, htr137a, htr237a, htr345a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hd03a, hd45b, htr038a, htr134a, htr138a, htr345a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr134c, htr145a, htr346a, htr456c])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134c, htr146a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr016c, htr068a, htr168a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, htr123b, htr138a, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hc012yz, htr024b, htr047a, htr124a, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr124c, htr147a, htr234b, htr247a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, hc012yz, htr024b, htr048a, htr124a, htr248a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr124c, htr148a, htr234b, htr248a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr026c, htr068a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr023a, htr234b, htr247a, htr345a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr023a, htr234b, htr248a, htr345a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc025xy, hc468zy, htr023a, htr056a, htr234a, htr348a, htr568a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, hc012yz, hc468zy, htr023a, htr026c, htr068a, htr126a, htr234a, htr348a])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc012yz, hc478zy, htr023a, htr127a, htr234a, htr278a, htr348a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc045yz, htr056a, htr136c, htr167a, htr346c, htr456c, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr023a, htr124a, htr126a, htr234b, htr256c, htr456a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr125a, htr126a, htr256c])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr023a, htr124a, htr125b, htr156a, htr234b, htr456a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc045yz, htr056a, htr156a, htr157a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, htr156a, htr158a, htr568c])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr125c, htr157a, htr257a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, htr256a, htr258a, htr568c])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hc045yz, htr058a, htr126a, htr128a, htr236c, htr258b, htr346c, htr456c])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    rcases m.htr 2 6 7 (by decide) (by decide) with
      ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
    ·
      linarith only [hlam, hd02a, hd67b, htr023a, htr124a, htr126a, htr234b, htr267a]
    ·
      linarith only [hlam, hc045yz, htr056a, htr236c, htr267a, htr346c, htr456c, htr567a]
  ·
    rcases m.htr 1 3 4 (by decide) (by decide) with
      ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, htr013a, htr014a, htr134b])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc145yz, htr013a, htr015a, htr134a, htr345a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc146yz, htr013a, htr016a, htr134a, htr346a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr013a, htr017a, htr134a, htr178a, htr345a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hd18a, hd45b, htr013a, htr018a, htr134a, htr345a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr013c, htr034a, htr134a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr013c, htr035a, htr134a, htr345b])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr134a, htr346b])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr013c, htr037a, htr134a, htr345a, htr378a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr014c, htr045a, htr134c, htr346a, htr456c])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr134c, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc016xy, hc456zy, htr013a, htr067a, htr134a, htr346a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc678yx, htr046b, htr047a, htr067a, htr457b, htr567b, htr568a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc046yz, hd01a, hd45b, htr013a, htr068a, htr134a, htr346a, htr456a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, htr134a, htr135a, htr345b])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr134a, htr136a, htr346b])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr134a, htr137a, htr345a, htr378a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr134c, htr145a, htr346a, htr456c])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr134c, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr016c, htr068a, htr168a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc246yz, hd01a, hd45b, htr013a, htr134a, htr268a, htr346a, htr456a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd01a, hd45b, htr013a, htr134a, htr345b, htr356a, htr456a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hd01a, hd45b, htr013a, htr134a, htr345b, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr356a, htr358a, htr568c])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr013a, htr134a, htr346a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc468yx, htr046b, htr048a, htr067a, htr467a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr034b, htr038c, htr048b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc678yx, htr056a, htr057a, htr567c, htr568a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr056a, htr058a, htr568c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hd03a, hd45b, htr038a, htr134a, htr138a, htr345a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc456zy, htr134c, htr147a, htr346a, htr467b, htr567a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015c, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015c, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr023b, htr038a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr124b, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc012xy, hc456zy, htr013a, htr025a, htr134a, htr256a, htr346a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr025c, htr057a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr256a, htr258a, htr568c])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc468zy, hd01a, hd46b, htr013a, htr134a, htr348a, htr467a, htr567a, htr568a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd23a, hd45b, htr023a, htr024b, htr048a, htr345a, htr348a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc235xy, hc246yz, htr023b, htr025a, htr026a, htr034b, htr048a, htr346a, htr348a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd46b, hd78a, htr026b, htr027a, htr067a, htr278a, htr467a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hd01a, hd45b, htr013a, htr134b, htr148a, htr345a, htr348a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hc235xy, htr023b, htr034b, htr048a, htr124c, htr125a, htr148a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr125a, htr126a, htr256c])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, htr125a, htr127a, htr257c])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr125a, htr128a, htr256c, htr268c])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc468yx, htr146b, htr148a, htr167a, htr467a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr024b, htr048a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd23a, hd45b, htr023a, htr028a, htr248c, htr345a, htr348a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      rcases m.htr 2 6 7 (by decide) (by decide) with
        ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd46b, htr023a, htr026a, htr267a, htr467a]
      ·
        linarith only [hlam, hc236xy, htr023a, htr026b, htr067a, htr267a]
    ·
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
        linarith only [hlam, htr127a, htr128a, htr278c])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hc123zy, htr134c, htr145a, htr234a, htr345a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr014a, htr017a, htr145a, htr178a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hc123zy, htr134c, htr146a, htr234a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd01a, hd45b, htr016a, htr168a, htr456a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr567a, htr568a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc678yx, htr246b, htr247a, htr267a, htr457b, htr567b, htr568a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc123zy, htr134a, htr234b, htr247a, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc123zy, htr014c, htr047a, htr134c, htr234a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc123zy, htr134c, htr147a, htr234a, htr347a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123zy, hc678yx, htr013a, htr018a, htr168b, htr234a, htr345b, htr356a, htr567a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
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
          linarith only [hlam, htr027a, htr028a, htr278c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc023zy, hc678yx, htr036a, htr234a, htr345b, htr356a, htr368a, htr567a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hd23a, hd45b, htr034a, htr036a, htr234a, htr356c, htr456a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr034a, htr035a, htr345b])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr034a, htr037a, htr347b])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc678yx, htr034a, htr038a, htr345b, htr356a, htr368b, htr567a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc458yx, htr034c, htr048a, htr345b, htr356a, htr456a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr035c, htr056a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr035c, htr057a, htr356a, htr567b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc678yx, htr035c, htr058a, htr356a, htr567a, htr568b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr036c, htr067a, htr356c, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hd23a, hd45b, htr134a, htr135a, htr234a, htr356a, htr456a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        rcases m.htr 1 3 6 (by decide) (by decide) with
          ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd45b, htr134a, htr136a, htr234a, htr356c, htr456a]
        ·
          linarith only [hlam, hc123zy, hc678yx, htr136a, htr234a, htr345b, htr356a, htr368a, htr567a]
      ·
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc678yx, htr356a, htr357a, htr567c, htr568a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr356a, htr358a, htr568c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc678yx, htr014a, htr018a, htr146a, htr168b, htr467a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc023zy, hc678yx, htr035a, htr234a, htr346a, htr356a, htr467a, htr568a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc023zy, hc678yx, htr036a, htr234a, htr346a, htr368a, htr467a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr034a, htr036a, htr234a, htr346c, htr467a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc678yx, htr034a, htr037a, htr134b, htr146a, htr357b, htr467a, htr567b, htr568a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc678yx, htr034a, htr038a, htr134b, htr146a, htr368b, htr467a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc678yx, htr014c, htr048a, htr146a, htr458b, htr467a, htr568b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc015xy, hc678yx, htr014a, htr056a, htr146a, htr467a, htr568a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, htr046c, htr067a, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hc123zy, hc678yx, htr135a, htr234a, htr346a, htr356a, htr467a, htr568a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          rcases m.htr 1 3 6 (by decide) (by decide) with
            ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd67b, htr134a, htr136a, htr234a, htr346c, htr467a]
          ·
            linarith only [hlam, hc035yz, htr056a, htr135a, htr136a, htr356b]
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hd23a, hd46b, htr023a, htr026a, htr267a, htr467a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc246yz, hd12b, hd68a, htr025a, htr026a, htr125a, htr467a, htr567a, htr568a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc246yz, htr026a, htr027a, htr267c, htr467a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr027a, htr028a, htr278c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc678yx, htr056a, htr057a, htr567c, htr568a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr056a, htr058a, htr568c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr056b, htr068a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc368zy, hd23a, hd46b, htr134a, htr138a, htr234a, htr467a, htr567a, htr568a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, htr015c, htr056a, htr156a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, htr015c, htr057a, htr157a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc468yx, htr246b, htr248a, htr267a, htr467a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, htr234b, htr238c, htr248b])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc123zy, htr013a, htr018a, htr138b, htr238a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc012xy, hc468zy, htr014a, htr025a, htr148a, htr256a, htr568a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc023zy, hd45b, hd68a, htr035a, htr145a, htr148a, htr234b, htr248a, htr356a, htr568a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc024yx, hd45b, hd68a, htr025a, htr048a, htr145a, htr148a, htr256a, htr568a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc123zy, htr034c, htr048a, htr134a, htr234b, htr248a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc123zy, htr034a, htr038a, htr138a, htr234a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc468yx, htr046b, htr048a, htr067a, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd35b, hd68a, htr035a, htr036c, htr067a, htr567a, htr568a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hc123zy, htr034a, htr035a, htr135a, htr234a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc123zy, htr034a, htr036a, htr136a, htr234a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr016c, htr067a, htr167a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hc678yx, htr256a, htr257a, htr567c, htr568a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr256a, htr258a, htr568c])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, htr256b, htr268a, htr568a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          rcases m.htr 3 4 8 (by decide) (by decide) with
            ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
          ·
            linarith only [hlam, hc123zy, htr134c, htr148a, htr234a, htr348a]
          ·
            linarith only [hlam, hc123zy, htr134a, htr234b, htr248a, htr348a]

theorem shard_043 {lam p : ℝ} (m : NineModel lam p)
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
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
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
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    : False :=
  proof_shard_043 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr346a htr346b htr346c htr236a htr236b htr236c htr246a htr246b htr246c htr457a htr457b htr457c htr568a htr568b htr568c

#print axioms shard_043
end Jsp404.NoSatNineDBMTerminal
