import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_181 {lam p : ℝ} (m : NineModel lam p)
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
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  have hd05a := (m.hrange 0 5 (by decide)).1
  obtain ⟨hd07a, hd07braw⟩ := m.hrange 0 7 (by decide)
  have hd07b : m.d 0 7 < (7/2 : ℝ)*lam := by
    linarith only [hd07braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  have hd15a := (m.hrange 1 5 (by decide)).1
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < (7/2 : ℝ)*lam := by
    linarith only [hd24braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < (7/2 : ℝ)*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
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
    linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr134a, htr234a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hc123xy, htr012a, htr013b, htr034a, htr134a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd12a, hd78b, htr125a, htr256a, htr567a, htr678a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  rcases m.htr 2 3 5 (by decide) (by decide) with
    ⟨htr235a, htr235b, htr235c, _, _⟩ | ⟨htr235a, htr235b, htr235c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc345xy, htr013a, htr014a, htr123c, htr134b, htr235a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc135yz, htr013a, htr015a, htr123c, htr235a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr013c, htr035a, htr123c, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc345xy, hd12a, hd78b, htr012a, htr013a, htr034a, htr035b, htr056a, htr123c, htr235a, htr567a, htr678a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc345xy, hd12a, hd78b, htr012a, htr013a, htr034a, htr035b, htr057a, htr123c, htr235a, htr567c, htr678a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc125xy, hd35b, hd56a, htr012a, htr013a, htr015c, htr057c, htr078a, htr123c, htr235a, htr567a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, htr123c, htr135a, htr235a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, htr015c, htr056a, htr156a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr015c, htr057a, htr157a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc127xy, hd35b, hd56a, htr012a, htr013a, htr123c, htr178a, htr235a, htr567a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr025c, htr057a, htr257a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hc456yx, htr123c, htr134a, htr235a, htr345c, htr346a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc345xy, htr024c, htr046a, htr234c, htr235a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, htr014b, htr016c, htr046b])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc345xy, htr124c, htr146a, htr234c, htr235a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc456zy, htr014a, htr017a, htr146a, htr157b, htr567b])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, htr017a, htr018a, htr178b])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc125xy, hc456zy, htr012a, htr014a, htr015c, htr056c, htr067a, htr146a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc345xy, hd12a, hd78b, htr012a, htr013a, htr034a, htr036b, htr067a, htr123c, htr235a, htr678a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc457yx, hd12a, hd78b, htr012a, htr013a, htr046b, htr047a, htr067a, htr123c, htr235a, htr345c, htr678a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc478yz, htr046b, htr048a, htr067a, htr678a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr067a, htr068a, htr678b])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013c, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc345xy, htr034b, htr047a, htr124c, htr147a, htr234c, htr235a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, hc345xy, htr034b, htr048a, htr124c, htr148a, htr234c, htr235a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    rcases m.htr 1 6 7 (by decide) (by decide) with
      ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
    ·
      linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a]
    ·
      linarith only [hlam, hc126xy, htr012a, htr014b, htr046b, htr067a, htr167a]
  ·
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr135a, htr235a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hc123xy, htr012a, htr013b, htr035a, htr135a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, htr235c, htr236b, htr256c])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr136a, htr236a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc123xy, htr012a, htr013b, htr036a, htr136a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      rcases m.htr 4 5 7 (by decide) (by decide) with
        ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
      ·
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
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc347xy, hd12a, hd78b, htr012a, htr013a, htr137a, htr345a, htr457a, htr567c, htr678a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc123xy, htr012a, htr013b, htr037a, htr137a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc348xy, hd12a, hd78b, htr012a, htr013a, htr138a, htr345a, htr457a, htr567c, htr678a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hd15a, hd78b, htr156a, htr456a, htr457a, htr567c, htr678a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc156zy, htr167a, htr456a, htr457a, htr567c])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr167a, htr168a, htr678b])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr167c, htr178a, htr678a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
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
          linarith only [hlam, hd12a, hd78b, htr124a, htr245a, htr457a, htr567c, htr678a])
        obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc234zy, htr025c, htr057a, htr245c, htr345a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr057a, htr058a, htr578b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc234zy, htr125c, htr157a, htr245c, htr345a, htr457a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr567c, htr678a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hc134zy, hc567xy, htr014a, htr015a, htr156a, htr345a, htr457a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hd56a, hd78b, htr015a, htr017a, htr156a, htr167c, htr678a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc123xy, hc567xy, htr012b, htr013a, htr015a, htr024b, htr045a, htr156a, htr457a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr045a, htr046a, htr456c])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc567xy, htr045a, htr047a, htr456a, htr457c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        rcases m.htr 1 4 5 (by decide) (by decide) with
          ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
        ·
          linarith only [hlam, hc134yx, htr013a, htr014c, htr045a, htr145a]
        ·
          linarith only [hlam, hd13b, hd34a, htr013a, htr014a, htr145a, htr345a]
      ·
        rcases m.htr 2 4 5 (by decide) (by decide) with
          ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
        ·
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, htr024c, htr045a, htr245a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, htr124c, htr145a, htr245a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          rcases m.htr 3 5 6 (by decide) (by decide) with
            ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
          ·
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hc345yz, hd12a, hd78b, htr012a, htr014a, htr124c, htr245a, htr356a, htr567a, htr678a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc345yz, htr024c, htr046a, htr245a, htr356a, htr456b])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc345yz, htr024c, htr047a, htr245a, htr356a, htr457b, htr567b])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc345yz, hc478yz, htr024c, htr048a, htr245a, htr356a, htr567a, htr678a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc235zy, htr026c, htr067a, htr256c, htr356a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr067a, htr068a, htr678b])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr067c, htr078a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hc347xy, htr013a, htr014a, htr134b, htr137a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hc123xy, htr012a, htr013b, htr037a, htr137a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, hc348xy, htr013a, htr014a, htr134b, htr138a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, htr014b, htr046a, htr146a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, htr014b, htr047a, htr147a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr014b, htr048a, htr148a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc235zy, htr126c, htr167a, htr256c, htr356a, htr567a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc123xy, hc345yz, htr013a, htr016a, htr124a, htr156b, htr245a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, htr015a, htr016a, htr156b])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc135yx, hc178yz, htr013a, htr018a, htr156a, htr567a, htr678a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr156a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, htr056a, htr057a, htr567b])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr056a, htr058a, htr568b])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, htr156a, htr157a, htr567b])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc345yz, htr016a, htr017a, htr136b, htr157c, htr356b, htr457a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr156a, htr158a, htr568b])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr237a, htr237b, htr237c, _, _⟩
              linarith only [hlam, htr013a, htr017a, htr123c, htr137b, htr237a])
            obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
            have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr238a, htr238b, htr238c, _, _⟩
              linarith only [hlam, htr123c, htr138a, htr238a])
            obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
            have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr246a, htr246b, htr246c, _, _⟩
              linarith only [hlam, hc345yz, htr245a, htr246a, htr356a, htr456b])
            obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hc345yz, htr245a, htr247a, htr356a, htr457b, htr567b])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, hc345yz, htr016a, htr018a, htr136b, htr148c, htr245a, htr248a, htr356b])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hc345yz, htr256a, htr257a, htr356a, htr457a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, hc235zy, htr016a, htr018a, htr136b, htr158c, htr258a, htr356b])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc235zy, htr256c, htr267a, htr356a, htr567a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr347a, htr347b, htr347c, _, _⟩
              linarith only [hlam, hd12a, hd78b, htr124a, htr247a, htr345b, htr347a, htr356a, htr567a, htr678a])
            obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, htr356a, htr357a, htr567b])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc135yx, htr013a, htr016a, htr136b, htr156a, htr367a, htr567a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr458a, htr458b, htr458c, _, _⟩
              linarith only [hlam, hc345yz, htr256a, htr258a, htr356a, htr458a])
            obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a]
            ·
              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr035b, htr056a, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, htr135b, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr458a, htr458b, htr458c, _, _⟩
              linarith only [hlam, hc123xy, hc568xy, htr124a, htr135a, htr245a, htr356a, htr458a])
            obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc347xy, hd56a, hd78b, htr035a, htr037a, htr346a, htr356a, htr467a, htr678a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hc348xy, hd56a, hd78b, htr035a, htr038a, htr346a, htr356a, htr467a, htr678a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hd07b, hd34a, htr078a, htr346a, htr467a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr137a, htr137b, htr137c, _, _⟩
                linarith only [hlam, htr013c, htr037a, htr137a])
              obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
              have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr138a, htr138b, htr138c, _, _⟩
                linarith only [hlam, htr013c, htr038a, htr138a])
              obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd17b, hd34a, htr178a, htr346a, htr467a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr237a, htr237b, htr237c, _, _⟩
                linarith only [hlam, htr013c, htr037a, htr123c, htr237a])
              obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
              have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr238a, htr238b, htr238c, _, _⟩
                linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
              obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
              have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
              obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc234zy, htr026c, htr067a, htr246c, htr346a, htr467a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, htr067a, htr068a, htr678b])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc234zy, htr126c, htr167a, htr246c, htr346a, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, htr167a, htr168a, htr678b])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                linarith only [hlam, hd34a, hd78b, htr246a, htr247a, htr346a, htr467c, htr678a])
              obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc045yz, htr057a, htr245a, htr247a, htr457b])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc145yz, htr157a, htr245a, htr247a, htr457b])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                linarith only [hlam, hc456yx, htr245b, htr246a, htr258a, htr458a])
              obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, hc123xy, hd56a, hd78b, htr013a, htr015a, htr126a, htr135b, htr267a, htr356a, htr678a])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, hc123xy, hc178yz, htr013a, htr018a, htr126a, htr267a, htr678a])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hc123xy, hd34a, hd78b, htr013a, htr016a, htr126a, htr146b, htr267a, htr346a, htr678a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr014a, htr014b, htr014c, _, _⟩
                linarith only [hlam, htr014a, htr016a, htr146b])
              obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
              have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                linarith only [hlam, hc134yx, htr013a, htr014c, htr046a, htr146a])
              obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, htr046a, htr047a, htr467b])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hc478yz, htr046a, htr048a, htr467a, htr678a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, htr146a, htr147a, htr467b])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr012a, htr017a, htr147c, htr245a, htr247a])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, htr014b, htr048a, htr148a])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr158a, htr458a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc125xy, htr012a, htr015b, htr058a, htr158a])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr248a, htr248b, htr248c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr012a, htr018a, htr148c, htr245a, htr248a])
              obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, htr267a, htr268a, htr678b])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr347a, htr347b, htr347c, _, _⟩
                linarith only [hlam, htr346a, htr347a, htr467b])
              obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc123xy, hd56a, hd78b, htr013a, htr017a, htr126a, htr157b, htr267a, htr356a, htr357a, htr678a])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              rcases m.htr 3 5 8 (by decide) (by decide) with
                ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
              ·
                linarith only [hlam, hc125xy, hd56a, hd78b, htr126a, htr158a, htr267a, htr356a, htr358a, htr678a]
              ·
                linarith only [hlam, hc123xy, hc578yz, htr126a, htr135a, htr267a, htr358a, htr678a]
            ·
              have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                linarith only [hlam, hd45b, hd56a, htr024c, htr046a, htr245a, htr467a, htr567a])
              obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc456zy, htr046a, htr047a, htr467b, htr567a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc456zy, htr035b, htr057a, htr356a, htr467a, htr567c])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, htr035c, htr037b, htr057c])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc456zy, htr047c, htr078a, htr467c, htr567a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, htr047b, htr048c, htr078b])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr137a, htr137b, htr137c, _, _⟩
                linarith only [hlam, htr013c, htr037a, htr137a])
              obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd45b, hd56a, htr124c, htr146a, htr245a, htr467a, htr567a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr014a, htr014b, htr014c, _, _⟩
                linarith only [hlam, hc123xy, hc456zy, htr012a, htr014a, htr135a, htr146a, htr356a])
              obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
              have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr138a, htr138b, htr138c, _, _⟩
                linarith only [hlam, hc348xy, htr013a, htr014a, htr134b, htr138a])
              obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hc123xy, htr012a, htr013b, htr038a, htr138a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, htr014b, htr047a, htr147a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, htr014b, htr048a, htr148a])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc456zy, htr135b, htr157a, htr356a, htr467a, htr567c])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc456zy, htr147c, htr178a, htr467c, htr567a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr237a, htr237b, htr237c, _, _⟩
                linarith only [hlam, htr013c, htr037a, htr123c, htr237a])
              obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
              have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr238a, htr238b, htr238c, _, _⟩
                linarith only [hlam, htr123c, htr138a, htr238a])
              obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
              have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                linarith only [hlam, hd45b, hd56a, htr245a, htr246a, htr467a, htr567a])
              obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, hc123xy, hc456zy, htr013a, htr015a, htr124a, htr135b, htr246a, htr356a])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr158a, htr458a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc125xy, htr012a, htr015b, htr058a, htr158a])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                linarith only [hlam, hc456zy, htr246a, htr247a, htr467b, htr567a])
              obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
              have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr248a, htr248b, htr248c, _, _⟩
                linarith only [hlam, hc123xy, hc456zy, htr012b, htr024b, htr048a, htr135a, htr246a, htr248a, htr356a])
              obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, htr025c, htr057a, htr257a])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                linarith only [hlam, htr125c, htr158a, htr258a])
              obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc123xy, hc456zy, htr126a, htr135a, htr267a, htr356a, htr467a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc456zy, htr247c, htr278a, htr467c, htr567a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr347a, htr347b, htr347c, _, _⟩
                linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr134b, htr247a, htr347a])
              obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
              have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr348a, htr348b, htr348c, _, _⟩
                linarith only [hlam, hc123xy, htr013a, htr014a, htr124a, htr134b, htr248a, htr348a])
              obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                linarith only [hlam, hc125xy, hc456zy, htr124a, htr158a, htr246a, htr356a, htr358a])
              obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hc123xy, hc578yz, htr012a, htr017a, htr135a, htr178a, htr358a])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc123xy, hc456zy, htr013a, htr017a, htr124a, htr167b, htr246a, htr567a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, htr016a, htr017a, htr167b])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, htr067a, htr068a, htr678b])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, htr167a, htr168a, htr678b])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc136yx, hc568yz, htr135a, htr167a, htr267a, htr268a, htr358a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, hc256zy, htr017a, htr018a, htr157b, htr168c, htr268a, htr567b])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, htr136b, htr167a, htr367a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, htr136b, htr167a, htr368a, htr678b])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr137b, htr278a, htr378a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, htr246c, htr268a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hc123xy, hc578yz, htr124a, htr135a, htr247a, htr358a, htr478a]
              ·
                linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a]
        ·
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc234zy, htr035b, htr056a, htr245a, htr345b, htr457a, htr567b])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc234zy, htr035b, htr057a, htr245a, htr345b, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr035c, htr037b, htr057c])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr013c, htr037a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc234zy, htr135b, htr156a, htr245a, htr345b, htr457a, htr567b])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc234zy, htr135b, htr157a, htr245a, htr345b, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, htr013c, htr037a, htr123c, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
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
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, htr245a, htr246a, htr456c])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, htr245a, htr247a, htr457c])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, htr245b, htr257a, htr457a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc234zy, htr245a, htr345b, htr356a, htr457a, htr567b])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc234zy, htr245a, htr345b, htr357a, htr457a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd03b, hd56a, htr037a, htr378a, htr567a, htr678a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd24b, hd56a, htr245a, htr457c, htr478a, htr567a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 4 6 7 (by decide) (by decide) with
            ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc234zy, htr026c, htr067a, htr245c, htr256c, htr346a, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr067a, htr068a, htr678b])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr067c, htr078a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc234zy, htr126c, htr167a, htr245c, htr256c, htr346a, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr167a, htr168a, htr678b])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, htr167c, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc234zy, htr245c, htr256c, htr267a, htr346a, htr467a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc123xy, hd56a, hd78b, htr013a, htr015a, htr126a, htr156a, htr267a, htr678a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc123xy, hc178yz, htr013a, htr018a, htr126a, htr267a, htr678a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr145a, htr145b, htr145c, _, _⟩
              linarith only [hlam, hc234zy, htr015a, htr016a, htr136b, htr145c, htr245a, htr346b])
            obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, htr014a, htr015a, htr145c])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc234zy, htr014b, htr016a, htr045a, htr136b, htr245a, htr346b])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, htr045a, htr046a, htr456c])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr045a, htr047a, htr457c])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            rcases m.htr 1 4 6 (by decide) (by decide) with
              ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
            ·
              linarith only [hlam, htr145a, htr146a, htr456c]
            ·
              linarith only [hlam, hc234zy, htr015a, htr016a, htr125c, htr146b, htr245c, htr346a]
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc234zy, htr036b, htr067a, htr245a, htr346b, htr456c, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc056zy, htr067c, htr078a, htr567a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc234zy, htr136b, htr167a, htr245a, htr346b, htr456c, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hd13b, hd56a, htr013a, htr015a, htr156c, htr167a, htr567a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hd13b, hd56a, htr013a, htr016a, htr167a, htr567a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hc124yz, hc156zy, htr014a, htr016a, htr245a, htr456c, htr467a, htr567a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc156zy, htr016a, htr017a, htr167b, htr567a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, htr017b, htr018c, htr078b])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc123xy, hc156zy, htr012a, htr013c, htr016a, htr034c, htr045a, htr456c, htr467a, htr567a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc234zy, htr045a, htr046a, htr245a, htr346a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd24b, hd56a, htr045a, htr047a, htr245a, htr467b, htr567a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, htr047a, htr048a, htr478b])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            rcases m.htr 1 4 5 (by decide) (by decide) with
              ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd24b, htr012a, htr014a, htr145a, htr245a]
            ·
              linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a]
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr034b, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, htr035b, htr056a, htr345b, htr346a, htr456b])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr134b, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr135b, htr156a, htr345b, htr346a, htr456b])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr234b, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hc567xy, htr345a, htr346a, htr456b, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc456yx, htr035b, htr057a, htr345b, htr346a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr035c, htr037b, htr057c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc456yx, htr135b, htr157a, htr345b, htr346a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr123c, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr025c, htr057a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc456yx, htr345b, htr346a, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd03b, hd56a, htr037a, htr378a, htr567a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc568xy, htr345a, htr346a, htr456b, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc456yx, htr035b, htr058a, htr345b, htr346a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr035c, htr038b, htr058c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc456yx, htr135b, htr158a, htr345b, htr346a, htr458a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr025c, htr058a, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc456yx, htr345b, htr346a, htr358a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc123xy, hc578yz, htr126a, htr135a, htr267a, htr358a, htr678a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc256zy, htr027c, htr078a, htr267c, htr567a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc256zy, htr127c, htr178a, htr267c, htr567a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc123xy, hc578yz, htr012a, htr017a, htr135a, htr178a, htr358a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr246c, htr247b, htr267c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc123xy, hc578yz, htr013a, htr015a, htr127a, htr158a, htr278a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr234a, htr346a, htr467a, htr567a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc246zy, htr034b, htr047a, htr267a, htr346a, htr467c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc246zy, htr134b, htr147a, htr267a, htr346a, htr467c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr245a, htr245b, htr245c, _, _⟩
        linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
      obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr245a, htr248a, htr458c])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc246zy, htr267a, htr346a, htr347a, htr467c])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc456yx, htr345a, htr346c, htr367a, htr467a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr367a, htr368a, htr678b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr467a, htr468a, htr678b])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc123xy, htr013a, htr017a, htr127a, htr147b, htr278a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
      ·
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc457yx, htr014a, htr017a, htr145a, htr147b])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc124xy, hc146zy, htr012a, htr016a, htr145a, htr345a, htr346a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045a, htr048a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc124xy, hc246zy, htr012b, htr026b, htr067a, htr145a, htr267a, htr345a, htr346a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr145a, htr148a, htr458c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        rcases m.htr 1 6 7 (by decide) (by decide) with
          ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
        ·
          linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a]
        ·
          linarith only [hlam, hd13b, hd56a, htr013a, htr016a, htr167a, htr567a]
      ·
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr014a, htr016a, htr146c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hd13b, hd46a, htr013a, htr014c, htr045a, htr345a, htr346a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        rcases m.htr 0 6 7 (by decide) (by decide) with
          ⟨htr067a, htr067b, htr067c, _, _⟩ | ⟨htr067a, htr067b, htr067c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc246zy, htr012b, htr013a, htr014a, htr026b, htr067a, htr134b, htr267a, htr346a]
        ·
          linarith only [hlam, hc456yx, htr045a, htr046c, htr067a, htr467a]

theorem shard_181 {lam p : ℝ} (m : NineModel lam p)
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
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    : False :=
  proof_shard_181 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr568a htr568b htr568c htr578a htr578b htr578c htr013a htr013b htr013c

#print axioms shard_181
end Jsp404.NoSatNineDBMTerminal
