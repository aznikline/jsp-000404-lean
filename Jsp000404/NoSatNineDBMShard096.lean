import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_096 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
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
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd05a := (m.hrange 0 5 (by decide)).1
  have hd07a := (m.hrange 0 7 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < (7/2 : ℝ)*lam := by
    linarith only [hd14braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd28a, hd28braw⟩ := m.hrange 2 8 (by decide)
  have hd28b : m.d 2 8 < (7/2 : ℝ)*lam := by
    linarith only [hd28braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < (7/2 : ℝ)*lam := by
    linarith only [hd38braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  rcases m.htr 1 3 4 (by decide) (by decide) with
    ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, htr013a, htr014a, htr134b])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr013c, htr034a, htr134a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd23a, hd34b, htr023a, htr024a, htr245a, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc234yz, htr024a, htr025a, htr245c, htr345a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234yz, htr013c, htr035a, htr134a, htr245a, htr345b])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, htr013b, htr015c, htr035b])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc234yz, htr025b, htr056a, htr245b, htr345a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr025c, htr026b, htr056c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc234yz, htr025b, htr057a, htr245b, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr025c, htr027b, htr057c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr012c, htr025a, htr125a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr012c, htr026a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, htr012c, htr027a, htr127a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc234yz, htr134a, htr135a, htr245a, htr345b])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015c, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015c, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc346yx, htr234b, htr236a, htr245a, htr345a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc347yx, htr234b, htr237a, htr245a, htr345a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc348yx, htr234b, htr238a, htr245a, htr345a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc012xy, hc568xy, htr013a, htr025a, htr135a, htr256a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr345c, htr348b, htr358c])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc234yz, htr245a, htr345c, htr358a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc234yz, htr025b, htr058a, htr245b, htr345a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr025c, htr028b, htr058c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr012c, htr028a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015c, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc234yz, htr245b, htr258a, htr345a, htr458a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc012xy, hc567yz, htr013a, htr025a, htr134b, htr146a, htr257a, htr467a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, htr026b, htr067a, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, htr026b, htr068a, htr268a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc012xy, hc567yz, htr013a, htr025a, htr136a, htr257a, htr367a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc346yx, htr013a, htr016a, htr134a, htr136b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, htr016a, htr017a, htr167b])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr016a, htr018a, htr168b])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc034yz, htr046a, htr134a, htr136a, htr346b])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc346yx, htr134b, htr136a, htr145a, htr345a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr145a, htr148a, htr458c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc012xy, hc567yz, htr016a, htr025a, htr167b, htr178a, htr257a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc234yz, htr134a, htr136a, htr246a, htr346b])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc012xy, hc567yz, htr016a, htr027a, htr167a, htr278a, htr578a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, htr136b, htr168a, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, hc346yx, htr136b, htr168a, htr245a, htr246a, htr345a, htr468a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd46a, hd67b, htr046a, htr047a, htr478a, htr678a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc467yz, htr047a, htr048a, htr478c, htr678a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hc234yz, htr135c, htr157c, htr178a, htr247a, htr345c, htr478a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc014xy, hc467yz, htr016a, htr045a, htr167a, htr245a, htr247a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc346yx, htr034b, htr036a, htr045a, htr345a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, htr036a, htr037a, htr367b])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr036a, htr038a, htr368b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd34b, hd57a, htr045a, htr047c, htr078a, htr345a, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hc346yx, hc347zy, htr136a, htr137a, htr245a, htr247a, htr345a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, hc567yz, htr137c, htr138a, htr178a, htr368c, htr578a, htr678c])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, hc234yz, htr045a, htr048a, htr248a, htr345a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            rcases m.htr 3 7 8 (by decide) (by decide) with
              ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
            ·
              linarith only [hlam, hc347yx, htr134a, htr137c, htr178a, htr378a]
            ·
              linarith only [hlam, hd34b, hd57a, htr134a, htr137a, htr378a, htr578a]
          ·
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd34b, hd57a, htr013c, htr037a, htr134a, htr347b, htr478a, htr578a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc346yx, hc357zy, htr036a, htr037a, htr345a, htr457c, htr478a, htr578a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr036a, htr038a, htr368b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc014xy, hc567yz, htr016a, htr045a, htr167a, htr457c, htr478a, htr578a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd34b, hd57a, htr045a, htr047a, htr345a, htr478a, htr578a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hd34b, hd57a, htr045a, htr048a, htr345a, htr478b, htr578a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc034yz, htr047b, htr078a, htr345a, htr457c, htr478a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            rcases m.htr 1 3 7 (by decide) (by decide) with
              ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
            ·
              linarith only [hlam, hc346yx, hc357zy, htr136a, htr137a, htr345a, htr457c, htr478a, htr578a]
            ·
              linarith only [hlam, hd34b, hd57a, htr134a, htr137a, htr347b, htr478a, htr578a]
        ·
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc126yx, hd34b, hd78a, htr012c, htr013a, htr016a, htr025a, htr134a, htr257a, htr578a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd34b, hd78a, htr013a, htr017a, htr134a, htr157b, htr578a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc128yx, hd34b, hd78a, htr012c, htr013a, htr018a, htr025a, htr134a, htr257a, htr578a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr057b, htr078a, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc012xy, hc378zy, htr013a, htr025a, htr138a, htr257a, htr578a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc023yx, hd34b, hd78a, htr025a, htr038a, htr134a, htr138a, htr257a, htr578a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc348yx, htr034b, htr038a, htr045a, htr345a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, htr045a, htr046a, htr456c])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, htr045a, htr047a, htr457c])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, htr014c, htr045a, htr145a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc012xy, hc678zy, htr016a, htr025a, htr168a, htr257a, htr578a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc012xy, htr017a, htr025a, htr178a, htr257a, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd34b, hd78a, htr245a, htr247a, htr345a, htr457b, htr578a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc234yz, htr013c, htr037a, htr134a, htr247a, htr347b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc348yx, htr037a, htr038a, htr134a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc234yz, htr134a, htr138a, htr248a, htr348b])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc348yx, hc356zy, htr036a, htr038a, htr245a, htr248a, htr345a, htr458b, htr568b])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc056zy, htr067a, htr247a, htr248a, htr458b, htr467c, htr568b])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc046yx, hc156zy, htr045a, htr068a, htr168a, htr245a, htr248a, htr458b, htr568b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr013c, htr036a, htr136a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc156zy, htr067a, htr068a, htr167a, htr568a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc234yz, htr013c, htr036a, htr134a, htr246a, htr346b])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hd34b, hd56a, htr013c, htr036a, htr134a, htr236c, htr268a, htr568a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd34b, hd56a, htr013c, htr036a, htr067a, htr068a, htr134a, htr367a, htr568a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            linarith only [hlam, hc346yx, htr013c, htr036c, htr068a, htr134a, htr368a]
          ·
            linarith only [hlam, hd34b, hd56a, htr013c, htr036a, htr134a, htr368a, htr568a]
      ·
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd34b, hd56a, htr013c, htr036a, htr134a, htr346b, htr467a, htr567a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr013b, htr016c, htr036b])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc356zy, htr036a, htr037a, htr347b, htr467b, htr567a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr013b, htr017c, htr037b])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc348yx, hc356zy, htr036a, htr038a, htr345a, htr456c, htr467a, htr567a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr013b, htr018c, htr038b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hd07a, hd34b, htr078a, htr345a, htr456c, htr467a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd34b, hd56a, htr134a, htr136a, htr346b, htr467a, htr567a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc014xy, hc356zy, htr013a, htr045a, htr136a, htr456c, htr467a, htr567a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd34b, hd56a, htr045a, htr046a, htr345a, htr467a, htr567a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hd34b, hd56a, htr045a, htr047a, htr345a, htr467b, htr567a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc034yz, htr046b, htr067a, htr345a, htr456c, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr067a, htr068a, htr678c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc034yz, hc356zy, htr047a, htr136a, htr137a, htr345a, htr347b, htr456c, htr467a, htr567a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc356zy, htr038c, htr068b, htr136a, htr138a, htr568a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr016c, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr016c, htr067a, htr168a, htr678c])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr017c, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr024b, htr046a, htr246a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr024b, htr047a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        rcases m.htr 2 6 7 (by decide) (by decide) with
          ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
        ·
          linarith only [hlam, hc234yz, htr246b, htr267a, htr345a, htr456c, htr467a]
        ·
          linarith only [hlam, hc012xy, hc356zy, htr013a, htr026a, htr136a, htr267a, htr567a]
    ·
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125yx, hd34b, hd56a, htr013a, htr015a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc126yx, hd34b, hd56a, htr013a, htr016a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127yx, hd34b, hd56a, htr013a, htr017a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128yx, hd34b, hd56a, htr013a, htr018a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hd05a, hd12b, htr056a, htr124a, htr245a, htr457a, htr567b])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd12b, hd56a, htr056a, htr057a, htr124a, htr245a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr124a, htr125a, htr245c])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc256zy, htr124a, htr126a, htr245a, htr456a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc257zy, htr124a, htr127a, htr245a, htr457a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hd28b, hd56a, htr124a, htr128a, htr245a, htr456a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr124b, htr145a, htr245a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr245a, htr456c])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr124b, htr147a, htr245a, htr457c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015c, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015c, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc127yx, hc567yz, htr124a, htr178a, htr245a, htr457a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr147c, htr148b, htr178c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr157c, htr158b, htr178c])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456c])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr245a, htr247a, htr457c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hd14b, hd56a, htr148a, htr245a, htr248a, htr456a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, htr245b, htr256a, htr457a, htr567b])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245b, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr134c, htr148a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd12b, hd56a, htr124a, htr245a, htr456c, htr467a, htr567a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd12b, hd56a, htr124a, htr245a, htr456c, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr124a, htr245a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567yz, htr057a, htr058a, htr578c, htr678a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc012xy, hc567yz, htr016a, htr024a, htr167a, htr245a, htr457a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hd12b, hd56a, htr024a, htr025a, htr124a, htr245b, htr456a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc012yz, hc567yz, htr026a, htr124a, htr126b, htr167a, htr245a, htr457a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc012yz, htr024b, htr045a, htr124a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr045a, htr047a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd12b, hd56a, htr045a, htr048a, htr124a, htr248a, htr456a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr025a, htr135a, htr235c])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc346yx, htr023a, htr024a, htr234c, htr236a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc234xy, htr023c, htr024a, htr036a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr036b, htr037c, htr067b])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr036b, htr038c, htr068b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr023b, htr037a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr023b, htr038a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr025c, htr058a, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12b, hd57a, htr024a, htr026a, htr124a, htr267a, htr578a, htr678a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc126yx, htr024a, htr026a, htr124a, htr168a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr025c, htr058a, htr235c, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc123yx, hc567yz, htr124a, htr136a, htr245a, htr367a, htr457a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc234xy, hc357zy, htr136a, htr137a, htr236a, htr245a, htr457a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr027a, htr137a, htr237c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd34b, hd57a, htr037c, htr078a, htr134a, htr137a, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr137c, htr138b, htr178c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr028a, htr138a, htr238c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr027b, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr136b, htr168a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      rcases m.htr 3 7 8 (by decide) (by decide) with
        ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
      ·
        linarith only [hlam, hc347yx, htr134a, htr137c, htr178a, htr378a]
      ·
        linarith only [hlam, hd34b, hd57a, htr134a, htr137a, htr378a, htr578a]
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr012a, htr014a, htr134b, htr345a, htr456a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, hc123zy, htr023a, htr024a, htr134a, htr234c])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hc123zy, htr023a, htr025a, htr134a, htr235c, htr345c])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc123zy, hc256zy, htr023a, htr026a, htr134a, htr345a, htr456a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc123zy, hc257zy, htr023a, htr027a, htr134a, htr345a, htr457a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hc123zy, htr024b, htr045a, htr134a, htr234b, htr345a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr045a, htr046a, htr456c])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, htr045a, htr047a, htr457c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045b, htr056a, htr457a, htr567b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr045b, htr057a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
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
      linarith only [hlam, htr012c, htr027a, htr127a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hc238xy, htr123c, htr128a, htr134a, htr234a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr024c, htr028a, htr045a, htr128a, htr456a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
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
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr134a, htr137a, htr347c])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hd38b, hd56a, htr134a, htr138a, htr345a, htr456a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr134b, htr145a, htr345a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134b, htr146a, htr345a, htr456c])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr134b, htr147a, htr345a, htr457c])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr135b, htr156a, htr235a, htr345a, htr457a, htr567b])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr135b, htr157a, htr235a, htr345a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc123zy, hc568xy, htr134a, htr135b, htr158a, htr235a, htr345a, htr456a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, htr145c, htr148b, htr158c])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hd14b, hd56a, htr045a, htr048a, htr148a, htr456a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc137yx, hc567yz, htr134a, htr178a, htr345a, htr457a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr234b, htr245a, htr345a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc027yx, hc567yz, htr024a, htr078a, htr245a, htr457a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, htr057c, htr058b, htr078c])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr245a, htr246a, htr456c])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr245a, htr247a, htr457c])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, hd14b, hd56a, htr148a, htr245a, htr248a, htr456a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr245b, htr256a, htr457a, htr567b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr245b, htr257a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, htr234c, htr248a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr158a, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr235b, htr258a, htr345c, htr358a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd13b, hd56a, htr134a, htr345c, htr358a, htr456a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd13b, hd56a, htr134a, htr345a, htr456c, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd13b, hd56a, htr134a, htr345a, htr456c, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr134a, htr345a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr178a, htr578a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc136yx, hc157zy, htr016a, htr017a, htr134a, htr345a, htr457a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc157zy, htr017a, htr018a, htr178b, htr578a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 1 6 7 (by decide) (by decide) with
      ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
    ·
      linarith only [hlam, hc012xy, hc567yz, htr016a, htr024a, htr167a, htr245a, htr457a]
    ·
      linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a]

theorem shard_096 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
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
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    : False :=
  proof_shard_096 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr457a htr457b htr457c htr347a htr347b htr347c htr357a htr357b htr357c htr568a htr568b htr568c htr023a htr023b htr023c

#print axioms shard_096
end Jsp404.NoSatNineDBMTerminal
