import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_203 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < (7/2 : ℝ)*lam := by
    linarith only [hd02braw, hp]
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < (7/2 : ℝ)*lam := by
    linarith only [hd04braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < (7/2 : ℝ)*lam := by
    linarith only [hd14braw, hp]
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < (7/2 : ℝ)*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc045yz, htr056a, htr345a, htr346a, htr456b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc145yz, htr156a, htr345a, htr346a, htr456b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr235a, htr236a, htr345b, htr346c])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr234b, htr246a, htr346a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr235b, htr256a, htr345b, htr346a, htr456b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc567xy, htr345a, htr346a, htr456b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc456yx, htr235b, htr257a, htr345b, htr346a, htr457a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr235c, htr237b, htr257c])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc456yx, htr345b, htr346a, htr357a, htr457a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr056a, htr057a, htr235a, htr357a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr156a, htr157a, htr235a, htr357a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc568xy, htr345a, htr346a, htr456b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc456yx, htr235b, htr258a, htr345b, htr346a, htr458a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr235c, htr238b, htr258c])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc456yx, htr345b, htr346a, htr358a, htr458a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr056a, htr058a, htr235a, htr358a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr156a, htr158a, htr235a, htr358a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr234a, htr346a, htr467a, htr567a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc456yx, htr345a, htr346c, htr367a, htr467a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd23b, hd56a, htr234a, htr346a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc456yx, htr345a, htr346c, htr368a, htr468a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 0 2 3 (by decide) (by decide) with
      ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
    ·
      rcases m.htr 1 3 4 (by decide) (by decide) with
        ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hc123yz, htr013a, htr014a, htr134c, htr234a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc123yz, htr023a, htr024a, htr134a, htr234b])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc123yz, htr023a, htr025a, htr134a, htr235b, htr345b])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc123yz, htr024c, htr045a, htr134a, htr234c, htr345a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc123yz, htr014b, htr046a, htr134b, htr234a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr014c, htr016b, htr046c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc456yx, htr045a, htr046c, htr067a, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc456yx, htr045a, htr046c, htr068a, htr468a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, htr123b, htr125a, htr134a, htr235b, htr345b])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc236yx, htr123b, htr126a, htr134a, htr234a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc237yx, htr123b, htr127a, htr134a, htr234a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc238yx, htr123b, htr128a, htr134a, htr234a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, htr134a, htr135a, htr345b])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc123yz, htr013a, htr015a, htr135c, htr235a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr015a, htr017a, htr157c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr015a, htr018a, htr158c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc456yx, htr134a, htr136a, htr345a, htr346b])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc123yz, htr023a, htr026a, htr136a, htr236b])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc123yz, htr023a, htr027a, htr136a, htr237b, htr367b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc123yz, htr023a, htr028a, htr136a, htr238b, htr368b])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr136a, htr137a, htr367b])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr136a, htr138a, htr368b])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, htr134c, htr145a, htr345a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc123yz, htr134b, htr146a, htr234a, htr346a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr016b, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr016b, htr068a, htr168a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr245a, htr245b, htr245c, _, _⟩
          linarith only [hlam, hc123yz, htr134a, htr234c, htr245a, htr345a])
        obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc123yz, hc456yx, htr136a, htr234a, htr245a, htr246c, htr267a, htr346a, htr368a, htr678c])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc123yz, hc456yx, htr136a, htr234a, htr245a, htr246c, htr268a, htr346a, htr368a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc123yz, hc567yz, htr136a, htr235a, htr237b, htr278a, htr357a, htr367b, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc123yz, htr136a, htr235c, htr257c, htr278a, htr367b, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc123yz, htr016b, htr067b, htr078a, htr136b, htr237a, htr378a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc123yz, htr137b, htr178a, htr237a, htr378a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc123yz, hc457yx, htr134a, htr237a, htr345a, htr378a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc123yz, hc678zy, htr134c, htr136a, htr147a, htr234a, htr368a, htr478a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc456yx, htr045a, htr047a, htr146a, htr147a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc456yx, htr146a, htr147a, htr245a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, htr234b, htr247a, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          linarith only [hlam, hc123yz, hc567yz, htr136a, htr237a, htr367a, htr378a, htr578a]
        ·
          linarith only [hlam, hc123yz, hc678zy, htr136a, htr235a, htr357a, htr368a, htr578a]
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, htr013a, htr014a, htr134c])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd15b, hd46a, htr013a, htr015a, htr134a, htr346a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr015a, htr016a, htr156c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr015a, htr017a, htr157c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr015a, htr018a, htr158c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, htr013b, htr034a, htr134a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc456yx, htr013b, htr035a, htr134a, htr345c, htr346a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, htr013b, htr036a, htr134a, htr346c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr035a, htr037a, htr357c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr035a, htr038a, htr358c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr014b, htr046a, htr134b, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hc456yx, htr134a, htr135a, htr345c, htr346a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc017yx, hc567yz, htr013a, htr078a, htr135a, htr357a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr134a, htr136a, htr346c])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr135a, htr137a, htr357c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr135a, htr138a, htr358c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hd01b, hd46a, htr013a, htr134c, htr145a, htr345a, htr346a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hc456yx, htr124b, htr125a, htr145a, htr235b, htr345b, htr346a])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr134b, htr146a, htr346a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc456yx, htr145a, htr146c, htr167a, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc456yx, htr145a, htr146c, htr168a, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr013a, htr026a, htr135a, htr267a, htr357a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr026b, htr068a, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd01b, hd57a, htr013a, htr135a, htr357c, htr378a, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc567yz, hd01b, hd46a, htr013a, htr135a, htr346a, htr347b, htr357a, htr378a, htr678a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr014b, htr047a, htr134b, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc456yx, htr045a, htr047c, htr078a, htr346b, htr367b, htr378a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hd23b, hd46a, htr023a, htr024c, htr045a, htr345a, htr346a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc236yx, hc247zy, htr023c, htr026a, htr027a, htr034c, htr045a, htr134b, htr145a, htr347a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc567yz, htr027c, htr028a, htr078a, htr268c, htr578a, htr678c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045a, htr048a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc236yx, htr023c, htr034c, htr045a, htr124b, htr126a, htr145a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, htr126a, htr127a, htr267b])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr126a, htr128a, htr268b])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr134b, htr147a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hd23b, hd57a, htr023a, htr027a, htr127c, htr178a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr245a, htr245b, htr245c, _, _⟩
          linarith only [hlam, htr024c, htr045a, htr245a])
        obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hd23b, hd46a, htr023a, htr025a, htr245b, htr345a, htr346a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024c, htr045a, htr248a, htr458c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hd23b, hd46a, htr023a, htr028a, htr134b, htr148a, htr248b, htr346a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        rcases m.htr 2 7 8 (by decide) (by decide) with
          ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
        ·
          linarith only [hlam, hc237yx, htr023a, htr027c, htr078a, htr278a]
        ·
          linarith only [hlam, hd23b, hd57a, htr023a, htr027a, htr278a, htr578a]
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, htr012c, htr014a, htr023a, htr124c, htr234c])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125xy, htr012c, htr015a, htr023a, htr123a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, htr015a, htr016a, htr156c])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, htr015a, htr017a, htr157c])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr015a, htr018a, htr158c])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, htr023a, htr024a, htr234c])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, htr023a, htr025a, htr235c])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr023a, htr026a, htr236c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr023a, htr027a, htr235c, htr257c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr023a, htr028a, htr235c, htr258c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr023b, htr034a, htr235a, htr345b])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr023b, htr035a, htr235a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc012zy, hc456yx, htr023a, htr024b, htr045a, htr124a, htr235a, htr345b, htr346a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr045a, htr047a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr045a, htr048a, htr458c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc027yx, hc567yz, htr023a, htr078a, htr235a, htr357a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hd02b, hd46a, htr023a, htr124a, htr125a, htr234c, htr235b, htr345b, htr346a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr134a, htr134b, htr134c, _, _⟩
        linarith only [hlam, hc012zy, htr023a, htr123b, htr134a, htr235a, htr345b])
      obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hd02b, hd46a, htr023a, htr134a, htr135a, htr235a, htr346a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr134a, htr136a, htr346c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr135a, htr137a, htr357c])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr135a, htr138a, htr358c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hd02b, hd46a, htr023a, htr124c, htr145a, htr234c, htr345a, htr346a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr134b, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc456yx, htr145a, htr146c, htr167a, htr467a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc456yx, htr145a, htr146c, htr168a, htr468a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      rcases m.htr 2 4 5 (by decide) (by decide) with
        ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
      ·
        linarith only [hlam, hc012zy, htr024c, htr045a, htr124a, htr245a]
      ·
        linarith only [hlam, hd02b, hd46a, htr023a, htr234c, htr245a, htr345a, htr346a]
  ·
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc123yz, hc168zy, htr013a, htr018a, htr234a, htr346a, htr456b, htr568a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr023a, htr023b, htr023c, _, _⟩
      linarith only [hlam, hd02b, hd68a, htr023a, htr235a, htr345b, htr346a, htr456b, htr568a])
    obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, hd23b, hd68a, htr023a, htr024a, htr234b, htr346a, htr456b, htr568a])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hd23b, hd68a, htr023a, htr025a, htr235b, htr345b, htr346a, htr456b, htr568a])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc023yz, hc678yx, htr036a, htr234a, htr346a, htr367a, htr456b, htr568a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, htr013c, htr016b, htr036c])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc456yx, htr034a, htr036a, htr345a, htr346b])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd14b, hd68a, htr013c, htr014a, htr034a, htr346a, htr456b, htr568a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hd15b, hd68a, htr013c, htr015a, htr034a, htr346a, htr456b, htr568a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, htr015a, htr017a, htr157c])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hd23b, hd68a, htr034a, htr035a, htr235a, htr346a, htr456b, htr568a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr035a, htr037a, htr357c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr035a, htr038a, htr358c])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hd04b, hd68a, htr045a, htr345a, htr346a, htr456b, htr568a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr034b, htr046a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc678yx, htr034b, htr047a, htr346a, htr456b, htr467c, htr568a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc468zy, htr034b, htr048a, htr346a, htr456b, htr568a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456yx, htr045a, htr046c, htr067a, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr056b, htr068a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr012b, htr025a, htr125a])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr013a, htr134a, htr346a, htr456b, htr568a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, hc236yx, htr123b, htr126a, htr134a, htr234a])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc237yx, htr123b, htr127a, htr134a, htr234a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hc238yx, htr123b, htr128a, htr134a, htr234a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, htr134a, htr135a, htr345b])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    rcases m.htr 1 3 6 (by decide) (by decide) with
      ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
    ·
      linarith only [hlam, hc123yz, hc678yx, htr136a, htr234a, htr346a, htr367a, htr456b, htr568a]
    ·
      linarith only [hlam, hc456yx, htr134a, htr136a, htr345a, htr346b]

theorem shard_203 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    : False :=
  proof_shard_203 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr346a htr346b htr346c

#print axioms shard_203
end Jsp404.NoSatNineDBMTerminal
