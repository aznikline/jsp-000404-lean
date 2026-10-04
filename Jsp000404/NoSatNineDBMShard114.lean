import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_114 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr578a : m.d 5 7 + lam ≤ m.d 7 8)
    (htr578b : m.d 5 7 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 7 8)
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
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd03a := (m.hrange 0 3 (by decide)).1
  have hd05a := (m.hrange 0 5 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd03a, hd78b, htr034a, htr346a, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr034a, htr035a, htr123a, htr235a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr034a, htr036a, htr346c, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hd05a, hd78b, htr056a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc056zy, htr067a, htr456a, htr457a, htr567c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr067a, htr068a, htr678b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr067c, htr078a, htr678a])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc256zy, hd34a, hd78b, htr123a, htr126a, htr234a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, htr013c, htr036a, htr136a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd15a, hd78b, htr156a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc156zy, htr167a, htr456a, htr457a, htr567c])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr167a, htr168a, htr678b])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr167c, htr178a, htr678a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr234a, htr236a, htr346c, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd25a, hd78b, htr256a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr123a, htr235c, htr257a, htr345a, htr457a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr123a, htr127a, htr234a, htr257c, htr567c, htr678a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr257a, htr258a, htr578b])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc568xy, htr123a, htr128a, htr235c, htr256a, htr258c])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr257c, htr278a, htr567c, htr678a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, htr346a, htr347a, htr456c, htr457b])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc478yz, htr346a, htr348a, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hc012yz, hc567xy, htr025a, htr123a, htr235a, htr257a, htr356a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr023a, htr023b, htr023c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr023a, htr025a, htr123a, htr256a])
  obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
  have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr016a, htr016b, htr016c, _, _⟩
    linarith only [hlam, hc012xy, hd56a, hd78b, htr016a, htr023a, htr167a, htr235a, htr356a, htr678a])
  obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
  have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr017a, htr017b, htr017c, _, _⟩
    linarith only [hlam, hc126yx, hd56a, hd78b, htr016a, htr017a, htr123a, htr167c, htr235a, htr356a, htr678a])
  obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, hc134zy, hc567xy, htr014a, htr017a, htr127b, htr256a, htr257b, htr345a, htr457a])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc568xy, htr023a, htr028a, htr235a, htr258c, htr356a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc567xy, htr035a, htr037a, htr347c, htr356a, htr457c])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc348xy, hc567xy, htr035a, htr038a, htr345a, htr356a, htr457a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc024yx, hc567xy, htr023a, htr045a, htr235a, htr356a, htr457a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, htr014c, htr015b, htr045c])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr045a, htr046a, htr456c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc567xy, htr045a, htr047a, htr456a, htr457c])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc034zy, htr045c, htr057a, htr345a, htr457a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr057a, htr058a, htr578b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, htr013a, htr014c, htr047a, htr137a, htr347c])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr013c, htr038a, htr138a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  rcases m.htr 1 4 5 (by decide) (by decide) with
    ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
  ·
    linarith only [hlam, hc124yx, htr012a, htr014c, htr045a, htr145a]
  ·
    linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr145a, htr345a]

theorem shard_114 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr578a : m.d 5 7 + lam ≤ m.d 7 8)
    (htr578b : m.d 5 7 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 7 8)
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
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False :=
  proof_shard_114 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr568a htr568b htr568c htr578a htr578b htr578c htr013a htr013b htr013c htr235a htr235b htr235c htr125a htr125b htr125c htr135a htr135b htr135c htr346a htr346b htr346c htr457a htr457b htr457c

#print axioms shard_114
end Jsp404.NoSatNineDBMTerminal
