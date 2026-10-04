import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_168 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
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
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < (7/2 : ℝ)*lam := by
    linarith only [hd06braw, hp]
  obtain ⟨hd07a, hd07braw⟩ := m.hrange 0 7 (by decide)
  have hd07b : m.d 0 7 < (7/2 : ℝ)*lam := by
    linarith only [hd07braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < (7/2 : ℝ)*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd27a, hd27braw⟩ := m.hrange 2 7 (by decide)
  have hd27b : m.d 2 7 < (7/2 : ℝ)*lam := by
    linarith only [hd27braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr012a, htr013b, htr034a, htr345a, htr456a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
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
    linarith only [hlam, htr013c, htr034a, htr134a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr012a, htr013a, htr135a, htr345c, htr456a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hc123xy, htr012a, htr013b, htr035a, htr135a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr235a, htr235b, htr235c, _, _⟩
    linarith only [hlam, htr123c, htr135a, htr235a])
  obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr345a, htr347a, htr457b])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr345c, htr357a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hd06b, hd34a, htr068a, htr345a, htr456a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd07b, hd34a, htr078a, htr345a, htr456a, htr568a, htr678c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr013a, htr136a, htr346c, htr456c, htr568a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr036a, htr136a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr013a, htr137a, htr347c, htr457c, htr567c, htr568a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr037a, htr137a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc348xy, hd12a, hd68b, htr012a, htr013a, htr138a, htr345a, htr456a, htr568a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd16b, hd34a, htr168a, htr345a, htr456a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd17b, hd34a, htr178a, htr345a, htr456a, htr568a, htr678c])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr123c, htr136a, htr236a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr123c, htr137a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr123c, htr138a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr245a, htr245b, htr245c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr124a, htr245a, htr457a, htr567c, htr568a])
      obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr056a, htr245c, htr345a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd34a, hd68b, htr056a, htr057a, htr345a, htr457a, htr568a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr056a, htr058a, htr568b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc234zy, htr125c, htr156a, htr245c, htr345a, htr456a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr015a, htr156a, htr568a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015b, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr156a, htr158a, htr568b])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd34a, hd68b, htr245a, htr246a, htr345a, htr456c, htr568a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hd34a, hd68b, htr245a, htr247a, htr345a, htr457c, htr567c, htr568a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc123xy, hc168yz, htr013a, htr018a, htr125a, htr256a, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hc123xy, hd34a, hd68b, htr013a, htr015a, htr125a, htr145b, htr256a, htr345a, htr568a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, htr014a, htr015a, htr145b])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc134yx, htr013a, htr014c, htr045a, htr145a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr045a, htr046a, htr456b])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr045a, htr047a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc468yz, htr045a, htr048a, htr457a, htr567c, htr568a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc234zy, hc678xy, htr046c, htr067a, htr246a, htr345a, htr456a, htr568a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr016b, htr067a, htr567a, htr568a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr145a, htr147a, htr457b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc234zy, htr015a, htr017a, htr135b, htr147c, htr247a, htr345b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr016b, htr067a, htr167a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc234zy, htr015a, htr018a, htr135b, htr148c, htr248a, htr345b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hd34a, hd68b, htr256a, htr257a, htr345a, htr457a, htr568a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr256a, htr258a, htr568b])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr126a, htr267a, htr567a, htr568a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, htr036b, htr067a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, htr457a, htr458a, htr567c, htr568b])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        linarith only [hlam, hd34a, hd68b, htr345a, htr456b, htr467a, htr567a, htr568a]
      ·
        linarith only [hlam, hc234zy, htr036b, htr067a, htr246a, htr346b, htr467a]
    ·
      rcases m.htr 2 4 5 (by decide) (by decide) with
        ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hd12a, hd56b, htr012a, htr014a, htr124c, htr245a, htr456a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc123xy, hc156yz, htr013a, htr016a, htr124a, htr245a, htr456a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc123xy, hc157yz, htr013a, htr017a, htr124a, htr245a, htr457a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, htr024c, htr045a, htr245a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr024c, htr046a, htr245a, htr456b])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr024c, htr047a, htr245a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr025c, htr056a, htr245c, htr457a, htr567c])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr025c, htr057a, htr245c, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc027xy, hc567zy, htr024a, htr078a, htr245a, htr457a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr017b, htr018c, htr078b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr014c, htr017b, htr048c, htr078b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr057b, htr058c, htr078b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc346xy, htr013a, htr014a, htr134b, htr136a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc123xy, htr012a, htr013b, htr036a, htr136a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc347xy, htr013a, htr014a, htr134b, htr137a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc123xy, hc356yz, htr036a, htr037a, htr124a, htr137a, htr245a, htr456a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc348xy, htr013a, htr014a, htr134b, htr138a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc123xy, hc356yz, htr036a, htr038a, htr124a, htr138a, htr245a, htr456a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr145a, htr245a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr146a, htr245a, htr456b])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr147a, htr245a, htr457b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr014b, htr048a, htr148a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr125c, htr156a, htr245c, htr457a, htr567c])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr125c, htr157a, htr245c, htr457a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr167a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc126xy, htr012a, htr016b, htr067a, htr167a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc567zy, hd12a, hd56b, htr067a, htr068a, htr124a, htr245a, htr457a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr016c, htr068a, htr168a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr157b, htr158c, htr178b])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr123c, htr136a, htr236a])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr123c, htr137a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr123c, htr138a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr245a, htr246a, htr456b])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr245a, htr247a, htr457b])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hd12a, hd56b, htr012a, htr018a, htr148c, htr245a, htr248a, htr456a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, htr245c, htr256a, htr457a, htr567c])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, htr245c, htr257a, htr457a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hd12a, hd56b, htr012a, htr018a, htr158c, htr245c, htr258a, htr456a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, htr126c, htr167a, htr267a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr026c, htr068a, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd12a, hd27b, htr012a, htr017a, htr178a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr035b, htr058a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 3 6 7 (by decide) (by decide) with
          ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
        ·
          linarith only [hlam, hc126xy, hc356yz, htr124a, htr167a, htr245a, htr367a, htr456a]
        ·
          linarith only [hlam, hc123xy, hc567zy, htr124a, htr136a, htr245a, htr367a, htr457a]
      ·
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc234zy, htr025c, htr056a, htr245c, htr345a, htr456a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc234zy, htr025c, htr057a, htr245c, htr345a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc234zy, htr125c, htr156a, htr245c, htr345a, htr456a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc234zy, htr125c, htr157a, htr245c, htr345a, htr457a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, hc346xy, htr234c, htr236a, htr245a, htr345a])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr136a, htr236a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc123xy, htr012a, htr013b, htr036a, htr136a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, hc347xy, htr234c, htr237a, htr245a, htr345a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr137a, htr237a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc123xy, htr012a, htr013b, htr037a, htr137a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc348xy, htr234c, htr238a, htr245a, htr345a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr138a, htr238a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc234zy, htr245c, htr257a, htr345a, htr457a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc123xy, hc567zy, htr125a, htr137a, htr257a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr347b, htr348c, htr378b])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr357b, htr358c, htr378b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hc234zy, htr245a, htr345b, htr358a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc234zy, htr025c, htr058a, htr245c, htr345a, htr458a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc234zy, htr125c, htr158a, htr245c, htr345a, htr458a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc234zy, htr245c, htr258a, htr345a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hd07b, hd34a, htr078a, htr345a, htr456b, htr467a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd17b, hd34a, htr178a, htr345a, htr456b, htr467a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr245a, htr246a, htr345a, htr467a, htr567a])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc234zy, htr026c, htr067a, htr246c, htr345a, htr456b, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc234zy, htr126c, htr167a, htr246c, htr345a, htr456b, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hd12a, hd56b, htr012a, htr015a, htr156b, htr167a, htr567a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr167a, htr567a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hc134zy, hc156yz, htr014a, htr016a, htr345a, htr456b, htr467a, htr567a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc156yz, htr016a, htr017a, htr167c, htr567a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc123xy, hc156yz, htr012b, htr013a, htr016a, htr024b, htr045a, htr456b, htr467a, htr567a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr045a, htr046a, htr345a, htr467a, htr567a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr045a, htr047a, htr345a, htr467c, htr567a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          rcases m.htr 1 4 5 (by decide) (by decide) with
            ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
          ·
            linarith only [hlam, hc134yx, htr013a, htr014c, htr045a, htr145a]
          ·
            linarith only [hlam, hd13b, hd34a, htr013a, htr014a, htr145a, htr345a]
        ·
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr125c, htr257a, htr578a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc123xy, hc178yz, htr013a, htr018a, htr125a, htr257a, htr578a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr057c, htr078a, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr145a, htr145b, htr145c, _, _⟩
              linarith only [hlam, hc123xy, hd34a, hd78b, htr013a, htr015a, htr125a, htr145b, htr257a, htr345a, htr578a])
            obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, htr014a, htr015a, htr145b])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc134yx, htr013a, htr014c, htr045a, htr145a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, htr045a, htr046a, htr456b])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr045a, htr047a, htr457b])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, htr045a, htr048a, htr458b])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, htr145a, htr146a, htr456b])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, htr145a, htr147a, htr457b])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr145a, htr148a, htr458b])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, htr157c, htr178a, htr578a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hd34a, hd78b, htr245a, htr247a, htr345a, htr457c, htr578a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc234zy, htr015a, htr017a, htr135b, htr147c, htr247a, htr345b])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, hc234zy, htr015a, htr018a, htr135b, htr148c, htr248a, htr345b])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc134yx, hc156yz, htr013a, htr016a, htr145a, htr245a, htr248a, htr458c, htr568c])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc056yz, htr067a, htr247a, htr248a, htr458c, htr467b, htr568c])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr016c, htr067a, htr167a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr168a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc126xy, htr012a, htr016b, htr068a, htr168a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr246a, htr246b, htr246c, _, _⟩
              linarith only [hlam, hc234zy, htr015a, htr016a, htr135b, htr146c, htr246a, htr345b])
            obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr126c, htr168a, htr268a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc134yx, hc356yz, htr013a, htr017a, htr145a, htr167b, htr245a, htr248a, htr367a, htr458c, htr568c])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 3 6 8 (by decide) (by decide) with
              ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
            ·
              linarith only [hlam, hc146xy, hc356yz, htr145a, htr168a, htr245a, htr248a, htr368a, htr458c, htr568c]
            ·
              linarith only [hlam, hc123xy, hc678yz, htr125a, htr136a, htr257a, htr368a, htr578a]
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc056yz, htr067a, htr567c, htr578a, htr678a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc567zy, htr067a, htr068a, htr578a, htr678c])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc156yz, htr167a, htr567c, htr578a, htr678a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc123xy, hc567zy, htr013a, htr016a, htr125a, htr167a, htr257a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr016c, htr068a, htr168a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, htr026c, htr067a, htr267a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr026c, htr068a, htr268a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc123xy, hc567zy, htr012a, htr015a, htr136a, htr157a, htr367a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc123xy, hc567zy, htr127a, htr136a, htr278a, htr367a, htr578a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hc567zy, htr367a, htr368a, htr578a, htr678c])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, htr346c, htr368a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            rcases m.htr 0 1 4 (by decide) (by decide) with
              ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
            ·
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc234zy, htr014b, htr015a, htr045a, htr135b, htr245a, htr345b])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              rcases m.htr 1 4 5 (by decide) (by decide) with
                ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
              ·
                linarith only [hlam, htr014c, htr045a, htr145a]
              ·
                linarith only [hlam, hc134zy, htr014a, htr015a, htr145b, htr345a]
            ·
              have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                linarith only [hlam, hc123xy, hc567zy, htr013a, htr014c, htr046a, htr125a, htr257a, htr467a])
              obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
              have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr145a, htr145b, htr145c, _, _⟩
                linarith only [hlam, hd13b, hd34a, htr013a, htr014a, htr145a, htr345a])
              obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc134yx, htr013a, htr014c, htr045a, htr145a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, htr045a, htr047a, htr457b])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, htr045a, htr048a, htr458b])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, htr014b, htr046a, htr146a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, htr145a, htr147a, htr457b])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, htr145a, htr148a, htr458b])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                linarith only [hlam, hc234zy, htr015a, htr016a, htr135b, htr146c, htr246a, htr345b])
              obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
              have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                linarith only [hlam, hc134yx, hc467zy, htr136a, htr145a, htr245a, htr247a, htr367a])
              obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hc234zy, htr015a, htr017a, htr135b, htr147c, htr247a, htr345b])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc234zy, htr047c, htr078a, htr247a, htr347b, htr378a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, htr017b, htr078a, htr178a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, hc234zy, htr015a, htr018a, htr135b, htr178c, htr247c, htr278a, htr345b])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr248a, htr248b, htr248c, _, _⟩
                linarith only [hlam, hc567zy, htr247c, htr248a, htr278a, htr458c, htr578c, htr678a])
              obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hc234zy, htr247c, htr278a, htr345a, htr457b, htr478a]
              ·
                linarith only [hlam, hc234zy, htr247a, htr347b, htr378a, htr478a]
  ·
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc056yz, htr067a, htr456a, htr457a, htr567b])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc156yz, htr167a, htr456a, htr457a, htr567b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd12a, hd56b, htr125a, htr257a, htr456a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, htr235c, htr237b, htr257c])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr137a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc123xy, htr012a, htr013b, htr037a, htr137a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr026c, htr067a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hc567yx, htr345a, htr347a, htr456a, htr457b])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc678xy, htr456a, htr457a, htr567b, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc567yx, htr456b, htr457a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc567yx, htr347c, htr378a, htr456a, htr457c, htr578a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, htr347b, htr348c, htr378b])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd12a, hd56b, htr012a, htr014a, htr124c, htr245a, htr456a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc123xy, hc156yz, htr013a, htr016a, htr124a, htr245a, htr456a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr024c, htr045a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr024c, htr046a, htr245a, htr456b])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc567yx, htr024c, htr047a, htr245a, htr456a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047a, htr048a, htr478b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, htr025c, htr056a, htr245c, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr047c, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc346xy, htr013a, htr014a, htr134b, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr036a, htr136a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc348xy, htr013a, htr014a, htr134b, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc123xy, hc356yz, htr036a, htr038a, htr124a, htr138a, htr245a, htr456a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr145a, htr245a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr146a, htr245a, htr456b])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014b, htr047a, htr147a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014b, htr047a, htr148a, htr478b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr125c, htr156a, htr245c, htr456a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr168a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc126xy, htr012a, htr016b, htr068a, htr168a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr147c, htr178a, htr478a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr123c, htr136a, htr236a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr123c, htr138a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456b])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc567yx, htr245a, htr247a, htr456a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc123xy, hc178yz, htr013a, htr018a, htr124a, htr247a, htr478a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr247a, htr248a, htr478b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, htr245c, htr256a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr126c, htr168a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc123xy, hc567yx, htr124a, htr135a, htr245a, htr357a, htr456a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr357a, htr358a, htr578b])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      rcases m.htr 3 6 8 (by decide) (by decide) with
        ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
      ·
        linarith only [hlam, hc126xy, hc356yz, htr124a, htr168a, htr245a, htr368a, htr456a]
      ·
        linarith only [hlam, hc123xy, hc678yz, htr124a, htr136a, htr247a, htr368a, htr478a]
    ·
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr056a, htr245c, htr345a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc234zy, htr035b, htr057a, htr245a, htr345b, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc234zy, hc567yx, htr056a, htr057c, htr078a, htr245a, htr347a, htr457a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc234zy, htr125c, htr156a, htr245c, htr345a, htr456a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc234zy, htr135b, htr157a, htr245a, htr345b, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc567yx, htr156b, htr157a, htr168a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc234zy, hc567yx, htr156a, htr157c, htr178a, htr245a, htr347a, htr457a, htr478a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc346xy, htr234c, htr236a, htr245a, htr345a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr136a, htr236a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr036a, htr136a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr036c, htr038b, htr068c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hc567yx, htr245a, htr246a, htr456c, htr457a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr245a, htr247a, htr457c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr246a, htr248a, htr468c])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc123xy, hc567yx, htr013a, htr015a, htr125a, htr157a, htr256a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hc124yz, hc567yx, htr014a, htr015a, htr156a, htr245a, htr457a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, htr015a, htr016a, htr156b])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc567yx, htr015a, htr017a, htr156a, htr157b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr017a, htr018a, htr178b])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc123xy, hc567yx, htr012a, htr013c, htr015a, htr034c, htr045a, htr156a, htr457a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr045a, htr046a, htr456b])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc234zy, htr045a, htr047a, htr245a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047a, htr048a, htr478b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      rcases m.htr 1 4 5 (by decide) (by decide) with
        ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
      ·
        linarith only [hlam, hd12a, hd56b, htr012a, htr014a, htr145a, htr456a]
      ·
        linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a]

theorem shard_168 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
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
    : False :=
  proof_shard_168 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c

#print axioms shard_168
end Jsp404.NoSatNineDBMTerminal
