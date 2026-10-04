import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_059 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < (7/2 : ℝ)*lam := by
    linarith only [hd02braw, hp]
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < (7/2 : ℝ)*lam := by
    linarith only [hd06braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  have hd18a := (m.hrange 1 8 (by decide)).1
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  have hd38a := (m.hrange 3 8 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
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
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hc367yz, htr378a, htr567a, htr568a, htr678b])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc678yx, htr456a, htr458a, htr567a, htr568b])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hc467yz, htr478a, htr567a, htr568a, htr678b])
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
      linarith only [hlam, hc125yx, htr012b, htr015a, htr023a, htr123a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc126yx, htr012b, htr016a, htr023a, htr123a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc127yx, htr012b, htr017a, htr023a, htr123a])
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
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr023a, htr027a, htr123a, htr278a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr023c, htr034a, htr235a, htr345c])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr023c, htr035a, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc026xy, hc345zy, htr023a, htr067a, htr235a, htr456a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr134a, htr235a, htr345c])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr135a, htr235a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, hd02a, hd67b, htr023a, htr124b, htr145a, htr234b, htr456a, htr567a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr124c, htr125b, htr145c])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc012yz, hc345zy, htr023a, htr025c, htr056a, htr125a, htr235a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr025b, htr026c, htr056b])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr035b, htr036c, htr056b])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc367yz, htr035b, htr037a, htr056a, htr567a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr025b, htr028c, htr058b])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr035b, htr038c, htr058b])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr567a, htr568a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hc012yz, htr023b, htr036a, htr123a, htr236a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr136a, htr236a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hc012yz, htr023b, htr037a, htr123a, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr137a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, hc012yz, htr023b, htr038a, htr123a, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc012yz, hc378zy, htr023a, htr024c, htr047a, htr124a, htr238a, htr478a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr138a, htr238a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd02a, hd67b, htr023a, htr234b, htr245a, htr456a, htr567a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hc012yz, htr024b, htr045a, htr124a, htr245a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc012yz, hc345zy, htr023a, htr045a, htr047a, htr124c, htr147a, htr235a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc457xy, htr145c, htr147a, htr156a, htr456a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc457xy, htr145c, htr147a, htr158a, htr458a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr156c, htr167a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr124b, htr147a, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc457xy, htr124a, htr127a, htr245a, htr247c])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc012yz, hc678yx, htr023a, htr027c, htr067b, htr068a, htr123b, htr127a, htr135b, htr156a, htr567a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd45a, hd67b, htr045a, htr046b, htr068a, htr567a, htr568a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, hc026yz, htr068a, htr126a, htr127c, htr167b, htr168a])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, htr127a, htr128a, htr278c])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    rcases m.htr 1 4 6 (by decide) (by decide) with
      ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
    ·
      linarith only [hlam, htr014c, htr046a, htr146a]
    ·
      linarith only [hlam, hc457xy, htr045b, htr056b, htr068a, htr146c, htr147a, htr168a]
  ·
    rcases m.htr 1 3 4 (by decide) (by decide) with
      ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, htr013a, htr014a, htr134b])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd34b, hd78a, htr013a, htr017a, htr134a, htr178a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr013c, htr034a, htr134a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr013a, htr134b, htr145a, htr456a, htr567a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr124c, htr125b, htr145c])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr013a, htr134a, htr348a, htr458c, htr567a, htr568c])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      rcases m.htr 2 4 5 (by decide) (by decide) with
        ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc234yz, htr013a, htr015a, htr134a, htr145b, htr245a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc156yz, hc234yz, htr013a, htr016a, htr134a, htr245a, htr456a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc234yz, hd18a, hd67b, htr013a, htr018a, htr134a, htr245a, htr456a, htr567a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr023a, htr024a, htr245a, htr456a, htr567a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr023a, htr025a, htr245c, htr456a, htr567a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc234yz, htr013c, htr035a, htr134a, htr245a, htr345b])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc234yz, htr013c, htr036a, htr134a, htr245a, htr346b, htr456b])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc234yz, htr013c, htr037a, htr134a, htr245a, htr348b, htr378c, htr458b])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc234yz, htr013c, htr038a, htr134a, htr245a, htr348b, htr458b])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc124zy, htr015c, htr056a, htr145c, htr245a, htr458a, htr568c])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr056a, htr057a, htr567b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hd24a, hd67b, htr056a, htr058a, htr245a, htr458a, htr567a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr056c, htr067a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc246xy, htr124c, htr126a, htr145a, htr245a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc247xy, htr124c, htr127a, htr145a, htr245a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr127a, htr128a, htr278c])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hc234yz, htr134a, htr135a, htr245a, htr345b])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc234yz, htr134a, htr136a, htr245a, htr346b, htr456b])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc234yz, htr134a, htr137a, htr245a, htr348b, htr378c, htr458b])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc234yz, htr134a, htr138a, htr245a, htr348b, htr458b])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc234yz, htr145a, htr146a, htr245a, htr346a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc234yz, htr145a, htr148a, htr245a, htr348a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc124zy, htr145c, htr156a, htr245a, htr458a, htr568c])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567b])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hd24a, hd67b, htr156a, htr158a, htr245a, htr458a, htr567a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr156c, htr167a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr567a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, hd01a, hd67b, htr013a, htr136a, htr234b, htr236a, htr245a, htr456a, htr567a])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hd01a, hd67b, htr013a, htr138a, htr234b, htr238a, htr245a, htr456a, htr567a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr245a, htr246a, htr456b])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc234yz, htr024a, htr026a, htr246c, htr346a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr245a, htr247a, htr457b])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr245a, htr248a, htr458b])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc234yz, htr024a, htr028a, htr248c, htr348a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, htr245c, htr256a, htr458a, htr568c])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, htr245c, htr257a, htr456a, htr567b])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr245c, htr258a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc234yz, htr245a, htr246c, htr267a, htr346a, htr458a, htr567a, htr568c])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc234yz, hc678yx, htr245a, htr246c, htr268a, htr346a, htr456a, htr567a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        rcases m.htr 3 5 6 (by decide) (by decide) with
          ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd67b, htr013a, htr135a, htr356a, htr567a]
        ·
          linarith only [hlam, hc234yz, htr245a, htr345c, htr356a, htr458a, htr568c]
      ·
        rcases m.htr 3 5 6 (by decide) (by decide) with
          ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
        ·
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr023a, htr025a, htr235c, htr356a, htr567a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, htr025b, htr045c, htr245b])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd06b, hd23a, htr067a, htr235a, htr356a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, hc236xy, hd45a, hd67b, htr124a, htr126a, htr235a, htr245a, htr356a, htr567a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hc237xy, hd45a, hd67b, htr124a, htr127a, htr235a, htr245a, htr356a, htr567a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr127a, htr128a, htr278c])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hd01a, hd67b, htr013a, htr135a, htr356a, htr567a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc123zy, htr013a, htr015a, htr135b, htr235a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc123zy, htr015c, htr056a, htr135c, htr235a, htr356a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr015b, htr016c, htr056b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr015b, htr018c, htr058b])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr135a, htr136a, htr235a, htr356c, htr567a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc034yz, htr046a, htr134a, htr136a, htr346b])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr134b, htr135a, htr148a, htr235a, htr458c, htr567a, htr568c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc123zy, htr135c, htr156a, htr235a, htr356a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, htr156a, htr157a, htr567b])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc678yx, htr156a, htr158a, htr567a, htr568b])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr156c, htr167a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr567a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr136c, htr138b, htr168c])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc034yz, htr048a, htr134a, htr138a, htr348b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr235a, htr236a, htr356b])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc123zy, htr023a, htr026a, htr136a, htr236c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc367yz, htr235a, htr237a, htr356a, htr567a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc348yx, htr134a, htr135a, htr235a, htr238a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc123zy, htr023a, htr028a, htr138a, htr238c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc234yz, htr134a, htr136a, htr246a, htr346b])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc234yz, htr134a, htr138a, htr248a, htr348b])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, htr235c, htr256a, htr356a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, htr235c, htr257a, htr356a, htr567b])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr025b, htr058a, htr258a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc123zy, htr136a, htr235a, htr236c, htr267a, htr356a, htr567a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc123zy, hc678yx, htr136a, htr235a, htr236c, htr268a, htr356a, htr567a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc467xy, htr134b, htr136c, htr147a, htr168a, htr246b, htr268a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, htr134c, htr147a, htr347a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, htr356a, htr357a, htr567b])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr135b, htr158a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc123zy, htr136a, htr235a, htr356a, htr367a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd67b, htr235a, htr356b, htr368a, htr567a, htr568a]
          ·
            linarith only [hlam, hd26a, hd34b, htr134a, htr136a, htr268a, htr368a]
        ·
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hd34b, hd45a, htr013c, htr035a, htr134a, htr356a, htr456a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, htr013b, htr015c, htr035b])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc345zy, htr035a, htr036a, htr356b, htr456a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr013b, htr016c, htr036b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc034yz, htr045a, htr345c, htr356a, htr458a, htr568c])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc345zy, htr045a, htr046a, htr356a, htr456c])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc345zy, htr045a, htr048a, htr356a, htr458c, htr568c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc345zy, htr036c, htr067a, htr356c, htr456a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr036b, htr037c, htr067b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc345zy, htr046b, htr068a, htr356a, htr456b, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hc268zy, hc345zy, htr124a, htr128a, htr245a, htr356a, htr568a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hd34b, hd45a, htr134a, htr135a, htr356a, htr456a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc128yx, hc345zy, htr013a, htr018a, htr124a, htr135a, htr245a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc345zy, htr135a, htr136a, htr356b, htr456a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc345zy, hc678yx, htr037c, htr067b, htr068a, htr135a, htr137a, htr456a, htr567a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, htr014c, htr046a, htr146a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr124c, htr126b, htr146c])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr014c, htr048a, htr148a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc345zy, htr136c, htr167a, htr356c, htr456a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr016c, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr023b, htr036a, htr236a])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, htr023b, htr037a, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc345zy, htr245a, htr246a, htr356a, htr456c])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc345zy, htr245a, htr248a, htr356a, htr458c, htr568c])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, htr126b, htr167a, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hc345zy, hc678yx, htr124a, htr127a, htr245a, htr267c, htr356a, htr568a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc345zy, htr246b, htr268a, htr356a, htr456b, htr568a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, hc457xy, htr345c, htr347a, htr356a, htr456a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc678yx, htr356a, htr357a, htr567c, htr568a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc345zy, htr045a, htr047a, htr357a, htr457c])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr014c, htr047a, htr147a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc345zy, htr245a, htr247a, htr357a, htr457c])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr356a, htr358a, htr568c])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc345zy, htr035a, htr038a, htr358b, htr458a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc345zy, htr135a, htr138a, htr358b, htr458a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr024a, htr024b, htr024c, _, _⟩
            linarith only [hlam, hc012xy, hc378zy, htr013a, htr024a, htr138a, htr247a, htr478a])
          obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hd12b, hd68a, htr024a, htr026a, htr124a, htr268a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc235yz, hc678yx, htr025a, htr026a, htr126b, htr167a, htr356a, htr568a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr026a, htr027a, htr267b])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc678yx, htr026a, htr028a, htr126b, htr167a, htr268b])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc012yz, hc678yx, htr024c, htr026a, htr045c, htr056a, htr124a, htr126b, htr167a, htr568a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc345zy, htr056a, htr058a, htr356a, htr458a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr023a, htr025a, htr125b, htr156a, htr567a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc345zy, htr156a, htr157a, htr357a, htr456a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr156a, htr158a, htr568c])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          rcases m.htr 2 5 6 (by decide) (by decide) with
            ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd67b, htr023a, htr025a, htr256a, htr567a]
          ·
            linarith only [hlam, hc235xy, htr023a, htr025b, htr056a, htr256a]
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hc123zy, htr013a, htr014a, htr134b, htr234a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr024a, htr134a, htr234c])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr025a, htr134a, htr235c, htr345c])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc123zy, htr024b, htr045a, htr134a, htr234b, htr346a, htr456b])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc123zy, htr024b, htr046a, htr134a, htr234b, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr024c, htr026b, htr046c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr123c, htr125a, htr134a, htr235c, htr345c])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr012c, htr026a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc237xy, htr123c, htr127a, htr134a, htr234a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr127a, htr128a, htr278c])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, htr134a, htr135a, htr345c])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc123zy, htr013a, htr015a, htr135b, htr235a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr134a, htr136a, htr346c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr134b, htr145a, htr346a, htr456b])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr134b, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr134a, htr235a, htr237a, htr345c, htr378a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr245a, htr245b, htr245c, _, _⟩
        linarith only [hlam, hc123zy, htr134a, htr234b, htr245a, htr346a, htr456b])
      obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr024a, htr027a, htr127a, htr245a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr027a, htr028a, htr278c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hc123zy, htr134a, htr234b, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd02b, hd45a, htr026a, htr267a, htr456a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd13b, hd45a, htr134a, htr346c, htr367a, htr456a, htr567a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc123zy, htr013a, htr016a, htr136b, htr235a, htr356b])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc123zy, hc167yz, htr013a, htr017a, htr235a, htr356a, htr567a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc123zy, htr014c, htr045c, htr056a, htr134c, htr235a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr056a, htr057a, htr567b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr015b, htr018c, htr058b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr056c, htr067a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc123zy, htr135c, htr156a, htr235a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567b])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc678yx, htr156a, htr158a, htr567a, htr568b])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr156c, htr167a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr136b, htr168a, htr235a, htr356b, htr567a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr136c, htr138b, htr168c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc678yx, htr146c, htr148a, htr168a, htr458c, htr567a, htr568c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc123zy, hd45a, hd67b, htr045a, htr048a, htr134c, htr148a, htr235a, htr356a, htr567a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr235a, htr236a, htr356b])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hd38a, hd67b, htr235a, htr238a, htr356a, htr567a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc123zy, hc467yz, htr134a, htr234c, htr235a, htr247a, htr356a, htr567a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc123zy, hd45a, hd67b, htr014c, htr047a, htr134c, htr235a, htr245a, htr247a, htr356a, htr567a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc123zy, hd45a, hd67b, htr134c, htr147a, htr235a, htr245a, htr247a, htr356a, htr567a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc467xy, htr046b, htr068a, htr146c, htr147a, htr168a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc123zy, hc678yx, htr034c, htr046c, htr068a, htr134a, htr235a, htr356a, htr567a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr034a, htr035a, htr345c])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc457xy, hc678yx, htr034a, htr037a, htr146c, htr147a, htr168a, htr345a, htr367c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr037a, htr038a, htr378c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr013c, htr037a, htr137a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc457xy, htr047a, htr048a, htr245a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, htr235c, htr256a, htr356a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr025b, htr058a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 2 6 8 (by decide) (by decide) with
          ⟨htr268a, htr268b, htr268c, _, _⟩ | ⟨htr268a, htr268b, htr268c, _, _⟩
        ·
          linarith only [hlam, hc467xy, htr146c, htr147a, htr168a, htr246b, htr268a]
        ·
          linarith only [hlam, hc123zy, hc678yx, htr134a, htr234c, htr235a, htr246c, htr268a, htr356a, htr567a]
      ·
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc145zy, htr015a, htr016a, htr136b, htr356b, htr456a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc137yx, hc145zy, htr015a, htr017a, htr134a, htr345c, htr356a, htr456a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc138yx, hc145zy, htr015a, htr018a, htr134a, htr345c, htr356a, htr456a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc013yz, hc678yx, htr036a, htr134a, htr345c, htr356a, htr367a, htr568a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hd13b, hd45a, htr034a, htr036a, htr134a, htr356b, htr456a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr034a, htr035a, htr345c])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc678yx, htr034a, htr037a, htr345c, htr356a, htr367c, htr568a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr037a, htr038a, htr378c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc457xy, htr034b, htr047a, htr345c, htr356a, htr456a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr034b, htr048a, htr345c, htr356a, htr458c, htr568c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr035b, htr056a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc678yx, htr035b, htr057a, htr356a, htr567c, htr568a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr035b, htr058a, htr356a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc045zy, htr056c, htr067a, htr456a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr036b, htr068a, htr356b, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr013c, htr037a, htr137a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr014c, htr047a, htr147a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr135b, htr156a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr015c, htr057a, htr157a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        rcases m.htr 1 6 7 (by decide) (by decide) with
          ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
        ·
          linarith only [hlam, hc013xy, hc678yx, htr016a, htr034a, htr167a, htr345c, htr356a, htr568a]
        ·
          linarith only [hlam, hc145zy, htr156c, htr167a, htr456a, htr567a]

theorem shard_059 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    : False :=
  proof_shard_059 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr346a htr346b htr346c htr568a htr568b htr568c

#print axioms shard_059
end Jsp404.NoSatNineDBMTerminal
