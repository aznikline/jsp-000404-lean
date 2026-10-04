import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_209 {lam p : ℝ} (m : NineModel lam p)
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
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr458a : m.d 5 8 + lam ≤ m.d 4 5)
    (htr458b : m.d 5 8 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 4 5)
    (htr468a : m.d 6 8 + lam ≤ m.d 4 6)
    (htr468b : m.d 6 8 < m.d 4 8)
    (htr468c : m.d 4 8 < m.d 4 6)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  have hd02a := (m.hrange 0 2 (by decide)).1
  have hd06a := (m.hrange 0 6 (by decide)).1
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
  have hd38a := (m.hrange 3 8 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
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
      linarith only [hlam, hc123yz, htr024c, htr045a, htr134a, htr234c, htr346a, htr456c])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc123yz, htr024c, htr046a, htr134a, htr234c, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr024b, htr026c, htr046b])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr123b, htr125a, htr134a, htr235b, htr345b])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, htr012b, htr026a, htr126a])
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
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr134a, htr136a, htr346b])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr134c, htr145a, htr346a, htr456c])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134c, htr146a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr234c, htr245a, htr346a, htr456c])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr024a, htr027a, htr127a, htr245a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr024a, htr028a, htr128a, htr245a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr234c, htr246a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr026a, htr267a, htr456a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd02a, hd45b, htr026a, htr268a, htr456a, htr568a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd13a, hd45b, htr134a, htr346b, htr367a, htr456a, htr567a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd13a, hd45b, htr134a, htr346b, htr368a, htr456a, htr568a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc145yz, htr015a, htr016a, htr136c, htr356c, htr456a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc137xy, hc145yz, htr015a, htr017a, htr134a, htr345b, htr356a, htr456a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc138xy, hc145yz, htr015a, htr018a, htr134a, htr345b, htr356a, htr456a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc123yz, htr025c, htr056a, htr134a, htr235c, htr345b, htr356a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc458yx, htr045b, htr048a, htr056a, htr456a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc045yz, htr056b, htr067a, htr456a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd37a, hd45b, htr134a, htr137a, htr345b, htr356a, htr456a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hd38a, hd45b, htr134a, htr138a, htr345b, htr356a, htr456a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014b, htr047a, htr147a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr135c, htr156a, htr356a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc145yz, htr156b, htr167a, htr456a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc145yz, htr156b, htr168a, htr456a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc345yz, htr235a, htr236a, htr356c, htr456a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc123yz, hd45b, hd67a, htr134a, htr137c, htr178a, htr236a, htr345b, htr356a, htr367c, htr456a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr236a, htr237a, htr367c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr236a, htr238a, htr368c])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc123yz, htr134a, htr235c, htr256a, htr345b, htr356a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc457yx, htr245b, htr247a, htr256a, htr456a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc458yx, htr245b, htr248a, htr256a, htr456a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr234b, htr247a, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr234b, htr248a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc123yz, htr137b, htr178a, htr236a, htr367c, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd13a, hd45b, htr056c, htr067c, htr078a, htr137a, htr378a, htr456a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc123yz, htr137a, htr236c, htr267c, htr278a, htr378a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        linarith only [hlam, hc012yx, hc678yz, htr016a, htr024a, htr168a, htr247a, htr478a]
      ·
        linarith only [hlam, hc123yz, hc467zy, htr137a, htr236a, htr367a, htr378a, htr478a]
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc123yz, htr013a, htr016a, htr136c, htr235a, htr356c])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc123yz, hc167zy, htr013a, htr017a, htr235a, htr356a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc123yz, hc168zy, htr013a, htr018a, htr235a, htr356a, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc123yz, htr014b, htr045b, htr056a, htr134b, htr235a, htr356a])
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
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr156a, htr157a, htr567c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr156a, htr158a, htr568c])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr156b, htr167a, htr568a, htr678b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr156b, htr168a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr235a, htr236a, htr356c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr235a, htr237a, htr356c, htr367c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr235a, htr238a, htr356c, htr368c])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc123yz, hc467zy, htr134a, htr234b, htr235a, htr247a, htr356a, htr567a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc123yz, hd45b, hd67a, htr014b, htr047a, htr134b, htr235a, htr245a, htr247a, htr356a, htr567a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc123yz, hd45b, hd67a, htr134b, htr147a, htr235a, htr245a, htr247a, htr356a, htr567a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc123yz, hc468zy, htr134a, htr234b, htr235a, htr248a, htr356a, htr568a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc457yx, htr047a, htr048a, htr245a, htr248a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc457yx, htr147a, htr148a, htr245a, htr248a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, htr235b, htr256a, htr356a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc012yx, hc678yz, htr015a, htr027a, htr156a, htr278a, htr568a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc457yx, htr047b, htr078a, htr245a, htr247c, htr278a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc457yx, htr147b, htr178a, htr245a, htr247c, htr278a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd23b, hd67a, htr134a, htr137c, htr178a, htr234a, htr678a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr134c, htr147a, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr134c, htr148a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc458yx, htr134a, htr138a, htr345a, htr348b])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr137c, htr178a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a]
      ·
        linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr478a, htr678a]
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, htr013a, htr014a, htr134c])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr013b, htr034a, htr134a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, hd01b, hd67a, htr013a, htr134c, htr145a, htr456a, htr567a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr124b, htr125c, htr145b])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd34a, hd45b, htr013b, htr035a, htr134a, htr356a, htr456a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, htr013c, htr015b, htr035c])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc345yz, htr035a, htr036a, htr356c, htr456a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr013c, htr016b, htr036c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr456a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc345yz, htr045a, htr046a, htr356a, htr456b])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc345yz, htr036b, htr067a, htr356b, htr456a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr013c, htr017b, htr036c, htr067c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr036c, htr037b, htr067c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc345yz, htr036b, htr068a, htr356b, htr456a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr013c, htr018b, htr036c, htr068c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr036c, htr038b, htr068c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr356a, htr456a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc345yz, htr135a, htr136a, htr356c, htr456a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr014b, htr046a, htr146a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, htr124b, htr126c, htr146b])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr136c, htr137b, htr167c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr136c, htr138b, htr168c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr023c, htr036a, htr236a])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr023c, htr037a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr023c, htr038a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, hc345yz, htr245a, htr246a, htr356a, htr456b])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, htr126c, htr167a, htr267a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr126c, htr168a, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc457yx, htr345b, htr347a, htr356a, htr456a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc458yx, htr345b, htr348a, htr356a, htr456a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd01b, hd67a, htr013a, htr137a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc015yx, hc678yz, htr013a, htr057a, htr136a, htr368a, htr578a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hc123xy, hc678yz, htr125a, htr136a, htr257a, htr368a, htr578a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          rcases m.htr 0 2 4 (by decide) (by decide) with
            ⟨htr024a, htr024b, htr024c, _, _⟩ | ⟨htr024a, htr024b, htr024c, _, _⟩
          ·
            have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr025a, htr025b, htr025c, _, _⟩
              linarith only [hlam, htr024a, htr025a, htr245b])
            obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, htr024a, htr026a, htr246b])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc012yx, hc345yz, htr015a, htr024a, htr156a, htr245a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hc457yx, htr145b, htr147a, htr156a, htr456a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, htr124b, htr127c, htr147b])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr024a, htr027a, htr127a, htr245a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hc458yx, htr145b, htr148a, htr156a, htr456a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, htr124b, htr128c, htr148b])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr024a, htr028a, htr128a, htr245a])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hc012yx, hc467zy, htr013a, htr024a, htr136a, htr247a, htr367a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc014yx, hc345yz, htr013a, htr047a, htr135a, htr245a, htr247a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc468zy, hd01b, hd34a, htr013a, htr047a, htr048a, htr136a, htr347a, htr368a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hc145yz, htr157a, htr245a, htr247a, htr457b])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, hc145yz, htr045a, htr048a, htr158a, htr458b])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr147c, htr178a, htr245a, htr247a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, htr024c, htr048a, htr248a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, htr025c, htr056a, htr256a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc012yx, hc678yz, htr013a, htr027a, htr136a, htr278a, htr368a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc457yx, htr047b, htr078a, htr245a, htr247c, htr278a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hc345yz, htr156a, htr157a, htr357a, htr456a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, hc345yz, htr156a, htr158a, htr358a, htr456a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a]
            ·
              linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr478a, htr678a]
          ·
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hc123xy, hc267zy, htr024a, htr027a, htr124a, htr136a, htr367a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, hc123xy, hc268zy, htr024a, htr028a, htr124a, htr136a, htr368a])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hc237yx, htr023a, htr024a, htr124a, htr127a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, hc238yx, htr023a, htr024a, htr124a, htr128a])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr124c, htr147a, htr347a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr124c, htr148a, htr348a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hd23b, hd67a, htr023a, htr027a, htr127c, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr247a, htr347a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr045a, htr047a, htr124a, htr247a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc467zy, hd01b, hd34a, htr013a, htr047a, htr048a, htr136a, htr348a, htr367a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, htr024b, htr048a, htr248a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd23b, hd67a, htr023a, htr027a, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc237yx, htr023a, htr027c, htr078a, htr278a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hc123xy, hc678yz, htr124a, htr136a, htr247a, htr368a, htr478a]
            ·
              linarith only [hlam, hc123xy, hc467zy, htr127a, htr136a, htr278a, htr367a, htr478a]
        ·
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr045a, htr047a, htr457b, htr578a, htr678a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc467zy, htr047a, htr048a, htr458b, htr578b, htr678a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc017yx, hc345yz, htr013a, htr078a, htr135a, htr456a, htr567c, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr014b, htr047a, htr147a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, htr124b, htr127c, htr147b])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr014b, htr048a, htr148a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr124b, htr128c, htr148b])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hd01b, hd67a, htr015a, htr156a, htr567c, htr578a, htr678a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr156a, htr157a, htr456a, htr578a, htr678a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr156a, htr158a, htr456a, htr578b, htr678a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc145yz, htr157b, htr178a, htr456a, htr567c, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr023a, htr026a, htr126c, htr167c, htr178a, htr678a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr023a, htr027a, htr127c, htr178a, htr678a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr024a, htr024b, htr024c, _, _⟩
            linarith only [hlam, hc123xy, hc267zy, htr024a, htr027a, htr124a, htr136a, htr367a])
          obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, htr024a, htr025a, htr245b])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc267zy, htr027a, htr028a, htr128c, htr178b, htr678a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          rcases m.htr 2 4 7 (by decide) (by decide) with
            ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
          ·
            linarith only [hlam, hc012yx, hc467zy, htr013a, htr024a, htr136a, htr247a, htr367a]
          ·
            linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr457b, htr578a, htr678a]
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc123yz, hc167zy, htr013a, htr017a, htr235a, htr356a, htr567a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123yz, hc168zy, htr013a, htr018a, htr235a, htr356a, htr568a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr023a, htr025a, htr235b, htr356a, htr567a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, htr025c, htr045b, htr245c])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hd06a, hd23b, htr067a, htr235a, htr356a, htr568a, htr678b])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr067a, htr068a, htr235a, htr356a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc236yx, hd45b, hd67a, htr124a, htr126a, htr235a, htr245a, htr356a, htr567a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc237yx, hd45b, hd67a, htr124a, htr127a, htr235a, htr245a, htr356a, htr567a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc238yx, hd45b, hd67a, htr124a, htr128a, htr235a, htr245a, htr356a, htr567a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc123yz, htr013a, htr015a, htr135c, htr235a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc123yz, htr015b, htr056a, htr135b, htr235a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr015c, htr016b, htr056c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr056a, htr057a, htr567c])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr056a, htr058a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr135a, htr136a, htr235a, htr356b, htr567a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc034zy, htr046a, htr134a, htr136a, htr346c])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567c])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr156a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr156b, htr167a, htr568a, htr678b])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr156b, htr168a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr235a, htr236a, htr356c])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc123yz, htr023a, htr026a, htr136a, htr236b])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, hc367zy, htr235a, htr237a, htr356a, htr567a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc368zy, htr235a, htr238a, htr356a, htr568a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, hc234zy, htr134a, htr136a, htr246a, htr346c])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, htr235b, htr256a, htr356a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, htr235b, htr257a, htr356a, htr567c])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr235b, htr258a, htr356a, htr568c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc123yz, htr136a, htr235a, htr236b, htr267a, htr356a, htr568a, htr678b])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc123yz, htr136a, htr235a, htr236b, htr268a, htr356a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc457yx, htr134a, htr135a, htr345c, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc345xy, htr134c, htr135a, htr147a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc458yx, htr134a, htr135a, htr345c, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc345xy, htr134c, htr135a, htr148a, htr348a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, htr356a, htr357a, htr567c])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr356a, htr358a, htr568c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc123yz, htr136a, htr235a, htr356a, htr367a, htr568a, htr678b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc123yz, htr136a, htr235a, htr356a, htr368a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr235a, htr356a, htr567c, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 0 2 4 (by decide) (by decide) with
          ⟨htr024a, htr024b, htr024c, _, _⟩ | ⟨htr024a, htr024b, htr024c, _, _⟩
        ·
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr024a, htr027a, htr127a, htr245a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr024a, htr028a, htr128a, htr245a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc012yx, hc467zy, htr015a, htr024a, htr156a, htr247a, htr567a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc234zy, htr013b, htr037a, htr134a, htr247a, htr347c])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc014yx, hd45b, hd67a, htr015a, htr047a, htr156a, htr245a, htr247a, htr567a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc345xy, htr034c, htr035a, htr047a, htr347a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr035a, htr036a, htr356c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr035a, htr038a, htr358c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc345xy, hc468zy, htr047a, htr048a, htr347a, htr356a, htr568a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc234zy, htr134a, htr137a, htr247a, htr347c])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc034zy, htr048a, htr134a, htr138a, htr348c])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr147c, htr178a, htr245a, htr247a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr024c, htr048a, htr248a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc012yx, hc678yz, htr015a, htr027a, htr156a, htr278a, htr568a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc457yx, htr047b, htr078a, htr245a, htr247c, htr278a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, htr137b, htr178a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a]
          ·
            linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr478a, htr678a]
        ·
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc234yx, hc267zy, htr024a, htr027a, htr235a, htr356a, htr567a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc234yx, hc268zy, htr024a, htr028a, htr235a, htr356a, htr568a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc234yx, htr023b, htr024a, htr035a, htr235a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr035a, htr036a, htr356c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc123yz, htr023a, htr027a, htr137a, htr237b])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc123yz, htr023a, htr028a, htr138a, htr238b])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr023a, htr027a, htr127c, htr178a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc457yx, htr024a, htr025a, htr245c, htr247a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr045a, htr047a, htr124a, htr247a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc345xy, hc467zy, htr047a, htr048a, htr348a, htr356a, htr567a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr024b, htr048a, htr248a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr023a, htr027a, htr278a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc237yx, htr023a, htr027c, htr078a, htr278a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc237yx, htr135a, htr137a, htr235a, htr278a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hc234yx, hc678yz, htr235a, htr247a, htr356a, htr478a, htr568a]
          ·
            linarith only [hlam, hc237yx, hc467zy, htr235a, htr278a, htr356a, htr478a, htr567a]
    ·
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc234zy, htr013a, htr015a, htr134a, htr145c, htr245a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc156zy, hc234zy, htr013a, htr016a, htr134a, htr245a, htr456a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc167zy, hc234zy, htr013a, htr017a, htr134a, htr245a, htr456a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc168zy, hc234zy, htr013a, htr018a, htr134a, htr245a, htr456a, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd23b, hd67a, htr023a, htr024a, htr245a, htr456a, htr567a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hd23b, hd67a, htr023a, htr025a, htr245b, htr456a, htr567a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234zy, htr013b, htr035a, htr134a, htr245a, htr345c])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc234zy, htr013b, htr036a, htr134a, htr245a, htr346c, htr456c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc234zy, hc367zy, htr013b, htr037a, htr134a, htr245a, htr456a, htr567a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc234zy, hc368zy, htr013b, htr038a, htr134a, htr245a, htr456a, htr568a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc124yz, htr015b, htr056a, htr145b, htr245a, htr456a])
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
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc246yx, htr124b, htr126a, htr145a, htr245a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc247yx, htr124b, htr127a, htr145a, htr245a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc248yx, htr124b, htr128a, htr145a, htr245a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc234zy, htr134a, htr135a, htr245a, htr345c])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc234zy, htr134a, htr136a, htr245a, htr346c, htr456c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc234zy, hc367zy, htr134a, htr137a, htr245a, htr456a, htr567a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc234zy, hc368zy, htr134a, htr138a, htr245a, htr456a, htr568a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hc234zy, htr145a, htr146a, htr245a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc124yz, htr145b, htr156a, htr245a, htr456a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr156a, htr157a, htr567c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr156a, htr158a, htr568c])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr156b, htr167a, htr568a, htr678b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr156b, htr168a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd01b, hd67a, htr013a, htr136a, htr234c, htr236a, htr245a, htr456a, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456c])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc234zy, htr024a, htr026a, htr246b, htr346a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr245a, htr247a, htr457c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr245a, htr248a, htr458c])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, htr245b, htr256a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245b, htr257a, htr456a, htr567c])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr245b, htr258a, htr456a, htr568c])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc234zy, htr245a, htr246b, htr267a, htr346a, htr456a, htr568a, htr678b])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc234zy, htr245a, htr246b, htr268a, htr346a, htr456a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        linarith only [hlam, hc234zy, htr245a, htr345b, htr356a, htr456a]
      ·
        linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a]

theorem shard_209 {lam p : ℝ} (m : NineModel lam p)
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
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr458a : m.d 5 8 + lam ≤ m.d 4 5)
    (htr458b : m.d 5 8 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 4 5)
    (htr468a : m.d 6 8 + lam ≤ m.d 4 6)
    (htr468b : m.d 6 8 < m.d 4 8)
    (htr468c : m.d 4 8 < m.d 4 6)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    : False :=
  proof_shard_209 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr346a htr346b htr346c htr568a htr568b htr568c htr458a htr458b htr458c htr468a htr468b htr468c htr023a htr023b htr023c

#print axioms shard_209
end Jsp404.NoSatNineDBMTerminal
