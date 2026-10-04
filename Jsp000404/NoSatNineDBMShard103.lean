import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_103 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd03a := (m.hrange 0 3 (by decide)).1
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < (7/2 : ℝ)*lam := by
    linarith only [hd06braw, hp]
  obtain ⟨hd07a, hd07braw⟩ := m.hrange 0 7 (by decide)
  have hd07b : m.d 0 7 < (7/2 : ℝ)*lam := by
    linarith only [hd07braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < (7/2 : ℝ)*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd03a, hd68b, htr034a, htr345a, htr457a, htr567c, htr568a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr034a, htr035a, htr123a, htr235a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hd06b, hd34a, htr068a, htr345a, htr456a, htr568a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, hd07b, hd34a, htr078a, htr345a, htr456a, htr568a, htr678c])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hd34a, hd68b, htr123a, htr126a, htr234a, htr256c, htr568a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hd34a, hd68b, htr123a, htr127a, htr234a, htr257c, htr567c, htr568a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd16b, hd34a, htr168a, htr345a, htr456a, htr568a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hd17b, hd34a, htr178a, htr345a, htr456a, htr568a, htr678c])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr257a, htr258a, htr567c, htr568b])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr256c, htr268a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr257c, htr278a, htr567c, htr568a, htr678c])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc468yz, htr345a, htr348a, htr457a, htr567c, htr568a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, htr345c, htr358a, htr456a, htr568b])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, htr346c, htr368a, htr456c, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, htr347c, htr378a, htr457c, htr567c, htr568a, htr678c])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, htr457a, htr458a, htr567c, htr568b])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd34a, hd68b, htr345a, htr456b, htr467a, htr567a, htr568a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc034zy, hc678xy, htr046a, htr345a, htr456a, htr467a, htr568a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hd34a, hd68b, htr045a, htr046a, htr345a, htr456c, htr568a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr045a, htr047a, htr457b])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr045a, htr048a, htr458b])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045c, htr056a, htr457a, htr567c])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr045c, htr057a, htr457a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc134zy, hc678xy, htr146a, htr345a, htr456a, htr467a, htr568a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hd34a, hd68b, htr145a, htr146a, htr345a, htr456c, htr568a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, hd01a, hd68b, htr014a, htr145a, htr457a, htr567c, htr568a])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, hd14a, hd68b, htr014a, htr015a, htr145c, htr457a, htr567c, htr568a])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr018a, htr018b, htr018c, _, _⟩
    linarith only [hlam, hc124yx, hc168yz, htr012a, htr018a, htr145a, htr457a, htr567c, htr568a])
  obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
  have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr023a, htr023b, htr023c, _, _⟩
    linarith only [hlam, hc124yx, htr012b, htr014a, htr023a, htr123a])
  obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hc124yx, hd34a, hd68b, htr023a, htr026a, htr126a, htr145a, htr234a, htr457a, htr567c, htr568a])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc124yx, hd34a, hd68b, htr023a, htr027a, htr127a, htr145a, htr234a, htr457a, htr567c, htr568a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc248xy, hd34a, hd68b, htr023a, htr028a, htr124b, htr145a, htr234a, htr457a, htr567c, htr568a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, htr012c, htr028a, htr128a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc346xy, htr013a, htr014a, htr124b, htr136a, htr234b])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc134yx, htr013b, htr014a, htr036a, htr136a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, hc347xy, htr013a, htr014a, htr124b, htr137a, htr234b])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc134yx, htr013b, htr014a, htr037a, htr137a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, hc348xy, htr013a, htr014a, htr124b, htr138a, htr234b])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc134yx, htr013b, htr014a, htr038a, htr138a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, htr145a, htr147a, htr457b])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, htr145a, htr148a, htr458b])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc124yx, htr012a, htr015a, htr145a, htr156a, htr457a, htr567c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc124yx, htr012a, htr015a, htr145a, htr157a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc134yx, hd34a, hd68b, htr136a, htr145a, htr234a, htr236a, htr457a, htr567c, htr568a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hc134yx, hd34a, hd68b, htr137a, htr145a, htr234a, htr237a, htr457a, htr567c, htr568a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  rcases m.htr 2 3 8 (by decide) (by decide) with
    ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
  ·
    linarith only [hlam, hc134yx, hd34a, hd68b, htr138a, htr145a, htr234a, htr238a, htr457a, htr567c, htr568a]
  ·
    linarith only [hlam, hc124yx, hc368yz, htr123a, htr145a, htr238a, htr457a, htr567c, htr568a]

theorem shard_103 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    : False :=
  proof_shard_103 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr235a htr235b htr235c htr125a htr125b htr125c htr135a htr135b htr135c htr256a htr256b htr256c htr457a htr457b htr457c htr257a htr257b htr257c htr347a htr347b htr347c htr357a htr357b htr357c htr568a htr568b htr568c

#print axioms shard_103
end Jsp404.NoSatNineDBMTerminal
