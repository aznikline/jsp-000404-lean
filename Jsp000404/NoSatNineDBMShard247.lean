import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_247 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
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
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
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
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < (7/2 : ℝ)*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
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
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr012a, htr123a, htr237a, htr378a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc678yx, htr456a, htr458a, htr567a, htr568b])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hc467yz, htr478a, htr567a, htr568a, htr678b])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr012a, htr124a, htr247a, htr478a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr247c, htr257b, htr457c])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc678yx, htr256a, htr257a, htr567c, htr568a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hd23a, hd67b, htr012b, htr025a, htr123a, htr256a, htr567a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, htr012c, htr015b, htr025c])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hd23a, hd67b, htr123a, htr125a, htr256a, htr567a])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr235b, htr236c, htr256b])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc678yx, htr256a, htr258a, htr567a, htr568b])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr235b, htr238c, htr258b])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, htr256c, htr267a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr567a, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc678yx, htr346c, htr348a, htr368a, htr458c, htr567a, htr568c])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  rcases m.htr 1 3 4 (by decide) (by decide) with
    ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
  ·
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc023zy, htr034a, htr234b, htr245a, htr346a, htr456b])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234yz, htr034a, htr035a, htr245a, htr345b])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc234yz, hc678yx, htr034a, htr036a, htr245a, htr368a, htr456a, htr567a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc234yz, htr034a, htr037a, htr245a, htr348b, htr378c, htr458b])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc234yz, htr034a, htr038a, htr245a, htr348b, htr458b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc234yz, htr035c, htr056a, htr245a, htr345c, htr458a, htr568c])
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
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, htr013b, htr035a, htr135a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr013b, htr036a, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc234yz, htr012a, htr016a, htr124a, htr136c, htr346c])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013b, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013b, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc234yz, htr012a, htr018a, htr124a, htr138c, htr346c, htr368c])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015b, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015b, htr056a, htr157a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015b, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr016b, htr056c, htr167a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456b])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc234yz, htr012b, htr026a, htr124a, htr246c, htr346a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc234yz, htr124a, htr126a, htr246c, htr346a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr245a, htr248a, htr458b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc234yz, htr012b, htr028a, htr124a, htr248c, htr348a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc234yz, htr124a, htr128a, htr248c, htr348a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc234yz, hc678yx, htr245a, htr246c, htr268a, htr346a, htr456a, htr567a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hc234yz, htr245a, htr345c, htr356a, htr458a, htr568c])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc137xy, hd23a, hd67b, htr012a, htr013b, htr017a, htr035a, htr123a, htr356a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc013yx, hc267yz, htr012a, htr035a, htr127a, htr356a, htr567a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc023yx, hd23a, hd67b, htr027a, htr035a, htr123a, htr127a, htr356a, htr567a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc247xy, htr024c, htr027a, htr045a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr045a, htr046a, htr456b])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr045a, htr048a, htr458b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc267xy, htr026c, htr027a, htr068a, htr268a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr014b, htr045a, htr145a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr016b, htr068a, htr168a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc234yz, htr124a, htr127a, htr247c, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd24a, hd67b, htr245a, htr356a, htr358a, htr458a, htr567a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      rcases m.htr 4 6 8 (by decide) (by decide) with
        ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
      ·
        linarith only [hlam, hd24a, hd67b, htr245a, htr456b, htr468a, htr567a, htr568a]
      ·
        linarith only [hlam, hc234yz, htr245b, htr256b, htr268a, htr346a, htr468a]
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd16b, hd45a, htr012a, htr016a, htr124a, htr245a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd17b, hd45a, htr012a, htr017a, htr124a, htr245a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr017a, htr018a, htr178c])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr012b, htr026a, htr124a, htr245a, htr256c, htr567a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc457xy, htr012b, htr027a, htr124a, htr245a, htr247c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr027a, htr028a, htr278c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr014b, htr045a, htr124b, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc045zy, htr057a, htr245a, htr247a, htr457c])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc678yx, htr056a, htr057a, htr567c, htr568a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr056c, htr067a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc016yx, hd45a, hd67b, htr012a, htr068a, htr124a, htr245a, htr567a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr124a, htr126a, htr245a, htr256c, htr567a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc457xy, htr124a, htr127a, htr245a, htr247c])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr127a, htr128a, htr278c])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc015yx, hc678yx, htr012a, htr056a, htr123c, htr136a, htr368a, htr567a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr124b, htr145a, htr245a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd01b, hd45a, htr012a, htr124c, htr147a, htr245a, htr247a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc457xy, hd01b, hd23a, htr012a, htr124a, htr134b, htr135a, htr147a, htr235a, htr245a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc457xy, htr134b, htr137a, htr147a, htr237c, htr245a, htr247b])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr015b, htr056a, htr135b, htr138a, htr238a, htr567a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015b, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015b, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr016b, htr056c, htr167a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc015yx, hc678yx, htr012a, htr056a, htr126a, htr268a, htr567a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc023zy, htr034a, htr235b, htr256b, htr268a, htr346c, htr368a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc023zy, htr036a, htr235b, htr256b, htr268a, htr368a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc236yz, hd23a, hd67b, htr035a, htr036a, htr235a, htr268a, htr567a, htr568a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc236yz, htr036a, htr037a, htr268a, htr368b, htr378c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc236yz, htr036a, htr038a, htr268a, htr368b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr245a, htr246b, htr268a, htr567a, htr568a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr014b, htr046a, htr124b, htr246a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc457xy, htr046c, htr047a, htr068a, htr245b, htr256b, htr268a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047a, htr048a, htr478c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr246a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc457xy, htr146c, htr147a, htr168a, htr245b, htr256b, htr268a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr034c, htr047a, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        linarith only [hlam, hc013yx, hd45a, hd67b, htr012a, htr035a, htr124a, htr245a, htr356a, htr567a]
      ·
        linarith only [hlam, hc235yz, htr056c, htr068a, htr256b, htr268a, htr356a]
  ·
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc146zy, htr012a, htr016a, htr123c, htr134a, htr346a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hd17b, hd23a, htr012a, htr017a, htr123c, htr134a, htr234a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, htr017a, htr018a, htr178c])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr012b, htr026a, htr123c, htr134a, htr236c, htr346c])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc237xy, htr012b, htr027a, htr123c, htr134a, htr234a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr012b, htr028a, htr123c, htr134a, htr238c, htr346c, htr368c])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr013b, htr034a, htr134a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr013b, htr035a, htr134a, htr345c])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr134a, htr346c])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr013b, htr038a, htr134a, htr346c, htr368c])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, htr014b, htr045a, htr134b, htr346a, htr456b])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014b, htr046a, htr134b, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr014b, htr048a, htr134b, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc015yx, hc678yx, htr012a, htr056a, htr123c, htr134a, htr346c, htr368a, htr567a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc457xy, htr045c, htr047a, htr056a, htr456a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr034c, htr037b, htr047c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc678yx, htr056a, htr057a, htr567c, htr568a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, htr056a, htr058a, htr568c])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc023zy, htr036c, htr067a, htr235b, htr256a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr036b, htr068a, htr368a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, htr123c, htr126a, htr134a, htr236c, htr346c])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc023zy, htr034c, htr047a, htr123c, htr127a, htr134a, htr234a, htr247c])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, htr123c, htr128a, htr134a, htr238c, htr346c, htr368c])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, htr134a, htr135a, htr345c])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr134a, htr136a, htr346c])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hc023zy, htr037a, htr134a, htr137a, htr234a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr134a, htr138a, htr346c, htr368c])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr134b, htr145a, htr346a, htr456b])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134b, htr146a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc023zy, htr034c, htr047a, htr134b, htr147a, htr234a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc023zy, htr035c, htr056a, htr135b, htr156a, htr235a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc045zy, htr057a, htr156a, htr157a, htr456a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, htr156a, htr158a, htr568c])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr016b, htr067a, htr167a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr136b, htr168a, htr368a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      linarith only [hlam, hd01b, hd24a, htr012a, htr123c, htr134a, htr245a, htr346a, htr456b]
    ·
      linarith only [hlam, hc045zy, htr057a, htr245a, htr247a, htr457c]

theorem shard_247 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
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
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
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
  proof_shard_247 m htr012a htr012b htr012c htr123a htr123b htr123c htr013a htr013b htr013c htr023a htr023b htr023c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr124a htr124b htr124c htr014a htr014b htr014c htr024a htr024b htr024c htr235a htr235b htr235c htr346a htr346b htr346c htr568a htr568b htr568c

#print axioms shard_247
end Jsp404.NoSatNineDBMTerminal
