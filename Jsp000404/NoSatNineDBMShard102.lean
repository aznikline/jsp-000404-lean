import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_102 {lam p : ℝ} (m : NineModel lam p)
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
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd03a := (m.hrange 0 3 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd03a, hd56b, htr034a, htr234a, htr235a, htr345c, htr456a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc034zy, htr045a, htr234a, htr235a, htr345c])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr045a, htr046a, htr456b])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045c, htr056a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hc345xy, htr123a, htr125a, htr234a, htr235c])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc134zy, htr145a, htr234a, htr235a, htr345c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr145a, htr146a, htr456b])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr145c, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr235a, htr236a, htr356b])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc346xy, htr123a, htr126a, htr234a, htr236c])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr235c, htr256a, htr345c, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457yx, htr234a, htr235a, htr345c, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr045a, htr047a, htr347a, htr456a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr145a, htr147a, htr347a, htr456a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr124b, htr147a, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458yx, htr234a, htr235a, htr345c, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr045a, htr048a, htr348a, htr456a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr145a, htr148a, htr348a, htr456a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, htr124b, htr148a, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr234a, htr235a, htr356b, htr367a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc056yz, hc346xy, htr067a, htr234a, htr235a, htr345c, htr367a, htr456a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc346xy, htr125b, htr156b, htr167a, htr234a, htr235b, htr367a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, htr126c, htr127b, htr167c])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, htr346c, htr367a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd34a, hd68b, htr234a, htr235a, htr345c, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr234a, htr235a, htr356b, htr368a, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hc056yz, hc346xy, htr068a, htr234a, htr235a, htr345c, htr368a, htr456a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc346xy, htr125b, htr156b, htr168a, htr234a, htr235b, htr368a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, htr126c, htr128b, htr168c])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hc346xy, htr234a, htr236b, htr268a, htr368a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, htr346c, htr368a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc567zy, hd12b, hd34a, htr012a, htr016a, htr167a, htr234a, htr235a, htr345c, htr457a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr023a, htr023b, htr023c, _, _⟩
      linarith only [hlam, hc012yz, hc567zy, htr023a, htr126a, htr235a, htr267a, htr345c, htr457a])
    obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, htr023a, htr024a, htr234c])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hc345xy, htr023a, htr025a, htr234a, htr235c])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc346xy, htr023a, htr026a, htr234a, htr236c])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc012xy, hc567zy, htr014a, htr026a, htr145a, htr267a, htr457a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc124yx, hc567zy, htr014a, htr015a, htr126a, htr145c, htr267a, htr457a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, htr026a, htr027a, htr267c])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr026a, htr028a, htr268c])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hc345xy, htr013b, htr015a, htr035a, htr125b, htr234a, htr235b])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc346xy, htr035a, htr036a, htr234a, htr235a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr036a, htr037a, htr367c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr036a, htr038a, htr368c])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr045c, htr057a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    rcases m.htr 1 3 5 (by decide) (by decide) with
      ⟨htr135a, htr135b, htr135c, _, _⟩ | ⟨htr135a, htr135b, htr135c, _, _⟩
    ·
      linarith only [hlam, htr013c, htr035a, htr135a]
    ·
      linarith only [hlam, hd12b, hd34a, htr012a, htr015a, htr135b, htr234a, htr235a]
  ·
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr125b, htr157a, htr234a, htr235b, htr456a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc567yx, hd12b, hd34a, htr012a, htr015a, htr157a, htr234a, htr235a, htr345c, htr456a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, htr015a, htr016a, htr156b])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc567yx, htr015a, htr017a, htr145c, htr157b, htr456a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr234a, htr235b, htr257a, htr456a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc124yx, hc567yx, htr014a, htr015a, htr125a, htr145c, htr257a, htr456a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, htr014a, htr018a, htr148b])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr023a, htr023b, htr023c, _, _⟩
      linarith only [hlam, hc012yz, hc567yx, htr023a, htr125a, htr235a, htr257a, htr345c, htr456a])
    obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, htr023a, htr024a, htr234c])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    rcases m.htr 0 2 5 (by decide) (by decide) with
      ⟨htr025a, htr025b, htr025c, _, _⟩ | ⟨htr025a, htr025b, htr025c, _, _⟩
    ·
      linarith only [hlam, hc345xy, htr023a, htr025a, htr234a, htr235c]
    ·
      linarith only [hlam, hc012xy, hc567yx, htr014a, htr025a, htr145a, htr257a, htr456a]

theorem shard_102 {lam p : ℝ} (m : NineModel lam p)
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
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False :=
  proof_shard_102 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr235a htr235b htr235c

#print axioms shard_102
end Jsp404.NoSatNineDBMTerminal
