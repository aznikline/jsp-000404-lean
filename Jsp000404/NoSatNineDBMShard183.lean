import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_183 {lam p : ℝ} (m : NineModel lam p)
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
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  have hd03a := (m.hrange 0 3 (by decide)).1
  have hd05a := (m.hrange 0 5 (by decide)).1
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd03a, hd78b, htr034a, htr346a, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, htr013c, htr014b, htr034c])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr034a, htr035a, htr345c, htr457a, htr567c, htr678a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, htr013c, htr015b, htr035c])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr034a, htr036a, htr346c, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr016a, htr016b, htr016c, _, _⟩
    linarith only [hlam, htr013c, htr016b, htr036c])
  obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
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
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc234zy, hc278yz, htr124a, htr128a, htr345a, htr457a, htr567c, htr678a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hd13a, hd78b, htr134a, htr346a, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr134a, htr135a, htr345c, htr457a, htr567c, htr678a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr134a, htr136a, htr346c, htr456c, htr457a, htr567c, htr678a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd15a, hd78b, htr156a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd01b, hd34a, htr015a, htr157a, htr345a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr017a, htr017b, htr017c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr013a, htr017a, htr134a, htr157c, htr567c, htr678a])
  obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr157a, htr158a, htr578b])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr018a, htr018b, htr018c, _, _⟩
    linarith only [hlam, hc568xy, htr013a, htr018a, htr135c, htr156a, htr158c])
  obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr157c, htr178a, htr567c, htr678a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr123c, htr136a, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd12a, hd78b, htr124a, htr245a, htr457a, htr567c, htr678a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hc234zy, htr124a, htr125a, htr245b, htr345a])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, htr125b, htr127c, htr157b])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hc347xy, htr234c, htr237a, htr245a, htr345a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hc348xy, htr234c, htr238a, htr245a, htr345a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr245a, htr246a, htr456c])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc234zy, htr124a, htr126a, htr246b, htr346a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc567xy, htr245a, htr247a, htr456a, htr457c])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr245b, htr256a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc234zy, htr245c, htr257a, htr345a, htr457a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr023a, htr023b, htr023c, _, _⟩
    linarith only [hlam, hc012zy, hc567xy, htr023a, htr125a, htr234c, htr245a, htr257a, htr456a])
  obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr245a, htr345a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hc234zy, htr024a, htr025a, htr245b, htr345a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr025a, htr026a, htr246b, htr257a, htr346a, htr567c, htr678a])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, htr025a, htr027a, htr257b])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc278yz, htr025a, htr028a, htr257a, htr567c, htr678a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr025c, htr057a, htr257a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr025c, htr058a, htr257a, htr578b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, hc012yx, hc378yz, htr013a, htr025a, htr138a, htr257a, htr567c, htr678a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc023xy, hd34a, hd78b, htr025a, htr038a, htr134a, htr138a, htr257a, htr567c, htr678a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc348xy, htr034c, htr038a, htr045a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hd34a, hd78b, htr045a, htr046a, htr346a, htr457a, htr567c, htr678a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr045a, htr047a, htr457b])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hc478yz, htr045a, htr048a, htr457a, htr567c, htr678a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr014b, htr046a, htr146a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr257a, htr258a, htr578b])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr257c, htr278a, htr567c, htr678a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, htr346a, htr347a, htr456c, htr457b])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc234zy, htr034a, htr037a, htr247a, htr347c])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, hc348xy, htr037a, htr038a, htr134a, htr137a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, htr034b, htr048a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc234zy, htr134a, htr138a, htr248a, htr348c])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  rcases m.htr 3 5 6 (by decide) (by decide) with
    ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
  ·
    linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr567c, htr678a]
  ·
    linarith only [hlam, hd23b, hd56a, htr135a, htr138a, htr238a, htr356a]

theorem shard_183 {lam p : ℝ} (m : NineModel lam p)
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
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False :=
  proof_shard_183 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr568a htr568b htr568c htr578a htr578b htr578c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr346a htr346b htr346c htr457a htr457b htr457c

#print axioms shard_183
end Jsp404.NoSatNineDBMTerminal
