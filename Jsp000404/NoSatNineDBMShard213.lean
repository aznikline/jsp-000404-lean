import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_213 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < (7/2 : ℝ)*lam := by
    linarith only [hd02braw, hp]
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < (7/2 : ℝ)*lam := by
    linarith only [hd04braw, hp]
  have hd07a := (m.hrange 0 7 (by decide)).1
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < (7/2 : ℝ)*lam := by
    linarith only [hd14braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < (7/2 : ℝ)*lam := by
    linarith only [hd16braw, hp]
  have hd17a := (m.hrange 1 7 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < (7/2 : ℝ)*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < (7/2 : ℝ)*lam := by
    linarith only [hd26braw, hp]
  have hd27a := (m.hrange 2 7 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < (7/2 : ℝ)*lam := by
    linarith only [hd35braw, hp]
  have hd37a := (m.hrange 3 7 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hd04b, hd78a, htr045a, htr456a, htr567a, htr678a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hd45b, hd78a, htr045a, htr046a, htr456b, htr567a, htr678a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, hd07a, hd45b, htr078a, htr456a, htr567a, htr678a])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hd14b, hd78a, htr145a, htr456a, htr567a, htr678a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hd45b, hd78a, htr145a, htr146a, htr456b, htr567a, htr678a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hd17a, hd45b, htr178a, htr456a, htr567a, htr678a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hd45b, hd78a, htr245a, htr246a, htr456b, htr567a, htr678a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hd27a, hd45b, htr278a, htr456a, htr567a, htr678a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr234b, htr246a, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hd37a, hd45b, htr378a, htr456a, htr567a, htr678a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc578zy, htr456a, htr458a, htr567a, htr678a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, htr456b, htr468a, htr567a, htr678c])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, htr457b, htr478a, htr567b, htr678a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, htr567a, htr568a, htr678c])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, htr567b, htr578a, htr678a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  rcases m.htr 0 1 3 (by decide) (by decide) with
    ⟨htr013a, htr013b, htr013c, _, _⟩ | ⟨htr013a, htr013b, htr013c, _, _⟩
  ·
    have hforced124 := (m.htr 1 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr124a, htr124b, htr124c, _, _⟩
      linarith only [hlam, hc234yx, htr012a, htr013a, htr123c, htr124a])
    obtain ⟨htr124a, htr124b, htr124c, _, _⟩ := hforced124
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, hc123xy, htr012c, htr013a, htr024a, htr124a])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, htr024a, htr025a, htr245b])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr024a, htr026a, htr246b])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hd45b, hd78a, htr024a, htr027a, htr245a, htr278a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr124a, htr125a, htr245b])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, htr124a, htr126a, htr246b])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, htr012b, htr027a, htr127a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
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
      linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr134a, htr234a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc123xy, htr012a, htr013b, htr034a, htr134a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hc378zy, hd12a, hd45b, htr012a, htr013a, htr138a, htr456a, htr567a, htr678a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, htr123c, htr138a, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr124a, htr246b, htr267a, htr456a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr267a, htr268a, htr678c])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    rcases m.htr 2 3 5 (by decide) (by decide) with
      ⟨htr235a, htr235b, htr235c, _, _⟩ | ⟨htr235a, htr235b, htr235c, _, _⟩
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hc345xy, htr013a, htr014a, htr123c, htr134b, htr235a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, htr014a, htr015a, htr145b])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, htr014a, htr016a, htr146b])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd35b, hd78a, htr013a, htr017a, htr123c, htr178a, htr235a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc358yx, htr013a, htr018a, htr123c, htr138b, htr235a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr013c, htr035a, htr123c, htr235a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      rcases m.htr 0 5 6 (by decide) (by decide) with
        ⟨htr056a, htr056b, htr056c, _, _⟩ | ⟨htr056a, htr056b, htr056c, _, _⟩
      ·
        linarith only [hlam, hc345xy, hd12a, hd45b, htr012a, htr013a, htr034a, htr035b, htr056a, htr123c, htr235a, htr456a]
      ·
        linarith only [hlam, hc125xy, hd35b, hd78a, htr012a, htr013a, htr015c, htr056a, htr123c, htr235a, htr567a, htr678a]
    ·
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr135a, htr235a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr035a, htr135a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc345yz, htr035a, htr036a, htr356c, htr456a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc345yz, htr036b, htr067a, htr356b, htr456a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr036c, htr037b, htr067c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr067a, htr068a, htr678c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr167a, htr168a, htr678c])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr123c, htr236a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc457yx, htr345b, htr347a, htr356a, htr456a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc458yx, htr345b, htr348a, htr356a, htr456a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr356a, htr357a, htr456a, htr567b, htr678a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc345yz, htr045a, htr047a, htr357a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc345yz, htr145a, htr147a, htr357a, htr457b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc345yz, htr245a, htr247a, htr357a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hc123xy, hd45b, hd78a, htr012a, htr013c, htr014a, htr036a, htr145a, htr367a, htr678a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc123xy, hc178zy, htr012a, htr013c, htr018a, htr036a, htr367a, htr678a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc468yx, htr014a, htr016a, htr146c, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc134yx, htr013a, htr014c, htr048a, htr148a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc123xy, hd45b, hd78a, htr012a, htr013c, htr016a, htr036a, htr156c, htr367a, htr456a, htr678a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, htr015a, htr016a, htr156c])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr056a, htr057a, htr567c])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr056a, htr058a, htr568c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr156a, htr157a, htr567c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc345yz, htr016a, htr017a, htr146c, htr157b, htr357a, htr456c])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr156a, htr158a, htr568c])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 2 4 8 (by decide) (by decide) with
        ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
      ·
        linarith only [hlam, hc123xy, hc478zy, htr013c, htr036a, htr124a, htr248a, htr367a, htr678a]
      ·
        linarith only [hlam, hc134yx, hd45b, hd78a, htr013c, htr036a, htr148a, htr245a, htr248a, htr367a, htr678a]
  ·
    rcases m.htr 1 2 4 (by decide) (by decide) with
      ⟨htr124a, htr124b, htr124c, _, _⟩ | ⟨htr124a, htr124b, htr124c, _, _⟩
    ·
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr124a, htr125a, htr245b])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr124a, htr126a, htr246b])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr124a, htr127a, htr245a, htr278a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12a, hd45b, htr124a, htr246b, htr267a, htr456a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr267a, htr268a, htr678c])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      rcases m.htr 2 3 5 (by decide) (by decide) with
        ⟨htr235a, htr235b, htr235c, _, _⟩ | ⟨htr235a, htr235b, htr235c, _, _⟩
      ·
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, htr123c, htr135a, htr235a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc457yx, htr234a, htr235a, htr345c, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc345xy, htr124c, htr147a, htr234c, htr235a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc345xy, htr234c, htr235a, htr247a, htr347a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr045a, htr047a, htr124a, htr247a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc458yx, htr234a, htr235a, htr345c, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc345xy, htr124c, htr148a, htr234c, htr235a, htr348a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hc478zy, hd12a, hd45b, htr012a, htr014a, htr148a, htr456a, htr567a, htr678a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr124b, htr128c, htr148b])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc345xy, htr234c, htr235a, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc012zy, hc478zy, htr026a, htr124a, htr248a, htr267a, htr678a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr045a, htr048a, htr124a, htr248a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc125xy, hc478zy, htr124a, htr156a, htr248a, htr567a, htr678a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc145yz, htr015a, htr016a, htr156c, htr456a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc145yz, hc178zy, htr015a, htr018a, htr456a, htr567a, htr678a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc145yz, htr016b, htr067a, htr156b, htr456a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc127xy, hc478zy, htr016c, htr017a, htr067a, htr124a, htr248a, htr678a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr067a, htr068a, htr678c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr135b, htr136c, htr156b])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hd45b, hd78a, htr135b, htr137a, htr156a, htr378a, htr456a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hd45b, hd78a, htr156a, htr157a, htr456a, htr567b, htr678a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc145yz, htr156b, htr167a, htr456a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc012yx, hc478zy, htr016a, htr024a, htr167a, htr248a, htr678a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr023a, htr023b, htr023c, _, _⟩
          linarith only [hlam, hc345xy, htr023a, htr024a, htr234b, htr235a])
        obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc345xy, htr023a, htr025a, htr234a, htr235c])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc278zy, hd12a, hd45b, htr024a, htr028a, htr124a, htr456a, htr567a, htr678a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, htr023b, htr034a, htr234a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc012zy, htr023c, htr035a, htr123a, htr235a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc345xy, hd26b, hd78a, htr023a, htr026a, htr035a, htr036a, htr136c, htr167a, htr234a, htr678a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc345xy, hd26b, hd78a, htr023a, htr026a, htr035a, htr037a, htr234a, htr378a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hd26b, hd78a, htr025c, htr026a, htr056a, htr567a, htr678a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc145yz, htr056a, htr057a, htr157a, htr456a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr134a, htr134b, htr134c, _, _⟩
          linarith only [hlam, hc012zy, htr023a, htr123b, htr134a, htr234a])
        obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr167a, htr168a, htr678c])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        rcases m.htr 2 3 6 (by decide) (by decide) with
          ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
        ·
          linarith only [hlam, hc346xy, htr023a, htr026a, htr234a, htr236c]
        ·
          linarith only [hlam, htr023b, htr036a, htr236a]
      ·
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc345yz, hc378zy, htr235a, htr238a, htr456a, htr567a, htr678a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, hc345yz, htr235a, htr236a, htr356c, htr456a])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr236c, htr237b, htr267c])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc457yx, htr345b, htr347a, htr356a, htr456a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc458yx, htr345b, htr348a, htr356a, htr456a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd45b, hd78a, htr356a, htr357a, htr456a, htr567b, htr678a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc345yz, htr045a, htr047a, htr357a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc345yz, htr145a, htr147a, htr357a, htr457b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc345yz, htr245a, htr247a, htr357a, htr457b])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hc123yz, hd45b, hd78a, htr013a, htr014a, htr145a, htr236a, htr367a, htr678a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123yz, hc178zy, htr013a, htr018a, htr236a, htr367a, htr678a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr023a, htr023b, htr023c, _, _⟩
          linarith only [hlam, hd02b, hd78a, htr023a, htr236a, htr367a, htr678a])
        obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr023a, htr026a, htr267a, htr678a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc023yz, hd45b, hd78a, htr034a, htr236a, htr345b, htr356a, htr367a, htr456a, htr678a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd34a, hd45b, htr034a, htr035a, htr356a, htr456a])
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
          linarith only [hlam, hd16b, hd78a, htr013c, htr016a, htr036a, htr367a, htr678a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc167zy, htr013c, htr017a, htr036a, htr367a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr036a, htr037a, htr367c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr036a, htr038a, htr367c, htr378c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr036b, htr067a, htr367a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr036b, htr068a, htr367a, htr678c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc238yx, hd45b, hd78a, htr124a, htr128a, htr236a, htr245a, htr367a, htr678a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr134a, htr134b, htr134c, _, _⟩
          linarith only [hlam, hc123yz, hd45b, hd78a, htr134a, htr236a, htr345b, htr356a, htr367a, htr456a, htr678a])
        obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr356a, htr456a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        rcases m.htr 1 3 6 (by decide) (by decide) with
          ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
        ·
          linarith only [hlam, hc345yz, htr135a, htr136a, htr356c, htr456a]
        ·
          linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a]
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, htr013a, htr014a, htr123b, htr124c])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc178zy, hd24a, hd45b, htr013a, htr018a, htr123b, htr124a, htr456a, htr567a, htr678a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, htr012b, htr024a, htr124a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr013b, htr034a, htr123b, htr124a, htr234b])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr235a, htr235b, htr235c, _, _⟩
        linarith only [hlam, hc345xy, htr123a, htr124a, htr234b, htr235a])
      obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234yx, htr013b, htr035a, htr123b, htr124a, htr235a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, htr013c, htr015b, htr035c])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc345yz, hc378zy, htr035a, htr038a, htr456a, htr567a, htr678a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc234yx, htr123b, htr124a, htr135a, htr235a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc345yz, htr013a, htr016a, htr135a, htr146c, htr456c])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc167zy, hc345yz, htr013a, htr017a, htr135a, htr456a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc016yx, hc345yz, htr013a, htr067a, htr135a, htr456a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr067a, htr068a, htr678c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc345yz, hc378zy, htr135a, htr138a, htr456a, htr567a, htr678a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hd01b, hd78a, htr015a, htr156a, htr567a, htr678a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc457yx, htr145b, htr147a, htr156a, htr456a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc458yx, htr145b, htr148a, htr156a, htr456a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr156a, htr157a, htr456a, htr567b, htr678a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc145yz, htr045a, htr047a, htr157a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc145yz, htr156b, htr167a, htr456a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr167a, htr168a, htr678c])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc346xy, htr123a, htr124a, htr234b, htr236a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc234yx, htr013b, htr036a, htr123b, htr124a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr036c, htr037b, htr067c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc234yx, htr123b, htr124a, htr136a, htr236a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd03b, hd78a, htr037a, htr136c, htr137a, htr167a, htr678a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr123c, htr137a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr123c, htr138a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr124b, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124b, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr124b, htr147a, htr234b, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr124b, htr148a, htr234b, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, htr135b, htr156a, htr356a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc345yz, htr236b, htr267a, htr356b, htr456a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr267a, htr268a, htr678c])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr135b, htr157a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      rcases m.htr 3 6 7 (by decide) (by decide) with
        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
      ·
        linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a]
      ·
        linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a]

theorem shard_213 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    : False :=
  proof_shard_213 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c

#print axioms shard_213
end Jsp404.NoSatNineDBMTerminal
