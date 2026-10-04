import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_194 {lam p : ℝ} (m : NineModel lam p)
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
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd03a := (m.hrange 0 3 (by decide)).1
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < (7/2 : ℝ)*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < (7/2 : ℝ)*lam := by
    linarith only [hd46braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < (7/2 : ℝ)*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc034zy, htr045a, htr234a, htr235a, htr345c])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, htr124a, htr125a, htr234c, htr235b])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, htr123c, htr135a, htr235a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, htr124c, htr145a, htr234c, htr235a, htr345c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc456yx, htr234a, htr235a, htr345c, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc345xy, htr124c, htr146a, htr234c, htr235a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, htr124b, htr126c, htr146b])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc345xy, htr234c, htr235a, htr246a, htr346a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr045a, htr046a, htr124a, htr246a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457yx, htr234a, htr235a, htr345c, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc345xy, htr124c, htr147a, htr234c, htr235a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, htr124b, htr127c, htr147b])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
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
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, htr124b, htr128c, htr148b])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc345xy, htr234c, htr235a, htr248a, htr348a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr045a, htr048a, htr124a, htr248a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr123a, htr235a, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd12a, hd67b, htr124a, htr247a, htr478a, htr678a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd12a, hd57b, htr012a, htr014a, htr124c, htr234c, htr235a, htr345c, htr457a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hc012zy, hc567xy, htr025a, htr123a, htr235a, htr256a, htr345c, htr457a])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr023a, htr023b, htr023c, _, _⟩
      linarith only [hlam, hc345xy, htr023a, htr025a, htr234a, htr235c])
    obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, hd12a, hd57b, htr023a, htr024a, htr124a, htr235a, htr345c, htr457a])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr024a, htr026a, htr246b])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, htr024a, htr027a, htr247b])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr024a, htr028a, htr248b])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hd03a, hd57b, htr034a, htr234a, htr235a, htr345c, htr457a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr023c, htr035a, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc567xy, htr023c, htr036a, htr235a, htr345c, htr356b, htr457a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc357yz, htr023c, htr037a, htr235a, htr345c, htr457a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc345xy, htr034a, htr035b, htr056a, htr356a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr045c, htr057a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr457c, htr478a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, hd13a, hd57b, htr134a, htr234a, htr235a, htr345c, htr457a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc345xy, htr013a, htr015a, htr125c, htr134a, htr235c])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc345xy, htr013a, htr016a, htr126c, htr134a, htr235c, htr256c])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc127xy, hc345xy, htr013a, htr017a, htr123a, htr134a, htr235a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc128xy, hc345xy, htr013a, htr018a, htr123a, htr134a, htr235a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013b, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    rcases m.htr 1 5 6 (by decide) (by decide) with
      ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
    ·
      linarith only [hlam, hc345xy, htr134a, htr135b, htr156a, htr356a]
    ·
      linarith only [hlam, hc012yx, hc567xy, htr015a, htr023a, htr156a, htr235a, htr345c, htr457a]
  ·
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr123a, htr235a, htr357a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr257a, htr357a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr457c, htr458b, htr478c])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr123a, htr235a, htr358a, htr458a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr258a, htr358a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      rcases m.htr 0 2 3 (by decide) (by decide) with
        ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
      ·
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc345xy, htr023a, htr024a, htr234b, htr235a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, htr023a, htr025a, htr235b])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, htr024a, htr026a, htr246b])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr024a, htr027a, htr247b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr024a, htr028a, htr248b])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr023c, htr035a, htr235a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hc123yz, htr013a, htr014a, htr134c, htr234a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr134a, htr136a, htr346b])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr134a, htr137a, htr347b])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr134a, htr138a, htr348b])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          rcases m.htr 4 6 7 (by decide) (by decide) with
            ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr046c, htr067a, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr146c, htr167a, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr236a, htr236b, htr236c, _, _⟩
              linarith only [hlam, hd13a, hd67b, htr134a, htr234a, htr236a, htr346c, htr467a])
            obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc123yz, htr013a, htr016a, htr136c, htr236a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc035yz, htr056a, htr235a, htr236a, htr356b])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc135yz, htr156a, htr235a, htr236a, htr356b])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hd35b, hd56a, htr136c, htr168a, htr235a, htr236a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, htr246c, htr267a, htr467a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc345xy, htr235a, htr236a, htr346a, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hd35b, hd56a, htr235a, htr236a, htr368a, htr568a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hd13a, hd67b, htr046c, htr068a, htr134a, htr346b, htr368a, htr467a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hd13a, hd67b, htr134a, htr246c, htr268a, htr346b, htr368a, htr467a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hd13a, hd67b, htr134a, htr346b, htr368a, htr467a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc045yz, htr057a, htr457c, htr478a, htr578a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc567yz, htr057a, htr058a, htr578c, htr678a])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc027xy, hc567yz, htr024a, htr078a, htr246a, htr467a, htr578a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc145yz, htr157a, htr457c, htr478a, htr578a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, hc012yx, hc567yz, htr015a, htr024a, htr157a, htr246a, htr467a])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hc125xy, hc167yz, htr015a, htr017a, htr124a, htr246a, htr467a])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, hc125xy, hc168yz, htr015a, htr018a, htr124a, htr246a, htr468a])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr034a, htr034b, htr034c, _, _⟩
                linarith only [hlam, hc135xy, htr013c, htr015a, htr034a, htr134a])
              obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, htr034a, htr036a, htr346b])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, htr015c, htr058a, htr158a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              rcases m.htr 1 7 8 (by decide) (by decide) with
                ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a]
              ·
                linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a]
            ·
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc345xy, hc678zy, htr023c, htr037a, htr235a, htr346a, htr357b, htr468a, htr578a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc025xy, hc678zy, htr024a, htr057a, htr246a, htr468a, htr578a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr034a, htr034b, htr034c, _, _⟩
                linarith only [hlam, hc345xy, htr034a, htr035b, htr057a, htr357a])
              obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, htr034a, htr036a, htr346b])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, htr034a, htr038a, htr348b])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc568yz, hd12a, hd45b, htr057a, htr058a, htr124a, htr246a, htr457a, htr468a])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc045yz, htr057b, htr078a, htr457a, htr578a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc125xy, hc678zy, htr124a, htr157a, htr246a, htr468a, htr578a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr157a, htr457a])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hc145yz, htr015a, htr017a, htr157c, htr457a])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, hc135yz, hc138xy, htr015a, htr018a, htr134a, htr234a, htr235a])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, htr015b, htr058a, htr158a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              rcases m.htr 1 7 8 (by decide) (by decide) with
                ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
              ·
                linarith only [hlam, hc145yz, htr157b, htr178a, htr457a, htr578a]
              ·
                linarith only [hlam, hc012yx, hc678zy, htr017a, htr024a, htr178a, htr246a, htr468a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr568a, htr678c])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc456zy, htr056a, htr057a, htr467a, htr567c])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc456zy, htr056a, htr058a, htr467a, htr568c, htr678c])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc456zy, htr057b, htr078a, htr467a, htr567b, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc145yz, htr156a, htr456c, htr467a, htr568a, htr678c])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hc456zy, htr156a, htr157a, htr467a, htr567c])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, hc456zy, htr156a, htr158a, htr467a, htr568c, htr678c])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc456zy, htr157b, htr178a, htr467a, htr567b, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, htr027c, htr078a, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, htr137c, htr178a, htr378a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, htr467a, htr468a, htr678c])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc012yx, hc478zy, htr015a, htr024a, htr157a, htr248a, htr578a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc125xy, hc478zy, htr015a, htr017a, htr124a, htr178a, htr248a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr034a, htr034b, htr034c, _, _⟩
              linarith only [hlam, hc135xy, htr013c, htr015a, htr034a, htr134a])
            obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, htr034a, htr036a, htr346b])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr034a, htr038a, htr348b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr237a, htr237b, htr237c, _, _⟩
              linarith only [hlam, hc123yz, htr013a, htr017a, htr137c, htr237a])
            obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc135xy, hc146yz, htr015a, htr016a, htr134a, htr234a, htr237a, htr347c, htr467c])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc135xy, hc456zy, htr015a, htr018a, htr134a, htr158b, htr234a, htr237a, htr347c, htr467c, htr568b])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc135xy, hc456zy, htr015c, htr056c, htr067a, htr134a, htr234a, htr237a, htr347c, htr467c, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc456zy, htr067a, htr068a, htr467a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            rcases m.htr 1 6 7 (by decide) (by decide) with
              ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr167a, htr467a]
            ·
              linarith only [hlam, hc126xy, htr012a, htr016b, htr067a, htr167a]
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, htr013a, htr014a, htr134c])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc345xy, htr013a, htr015a, htr125c, htr134a, htr235c])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc345xy, htr013a, htr016a, htr126c, htr134a, htr235c, htr256c])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc345xy, htr013a, htr017a, htr127c, htr134a, htr235c, htr257c])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc345xy, htr013a, htr018a, htr128c, htr134a, htr235c, htr258c])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, htr013b, htr034a, htr134a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc345xy, htr013b, htr035b, htr056a, htr134a, htr356a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc345xy, htr013b, htr035b, htr057a, htr134a, htr357a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc345xy, htr013b, htr035b, htr058a, htr134a, htr358a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc345xy, htr134a, htr135b, htr156a, htr356a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc345xy, htr134a, htr135b, htr157a, htr357a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc345xy, htr134a, htr135b, htr158a, htr358a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc012yx, hc456zy, htr016a, htr024a, htr167a, htr246a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc012yx, hc456zy, htr016a, htr024a, htr168a, htr246a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc012yx, hc567yz, htr015a, htr024a, htr157a, htr247b, htr278a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc012yx, hc567yz, htr015a, htr024a, htr157a, htr246a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc456zy, htr057b, htr078a, htr467a, htr567b, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc456zy, htr157b, htr178a, htr467a, htr567b, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc012yx, hc456zy, htr015a, htr024a, htr156a, htr246b, htr267a, htr467a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc345xy, htr134a, htr136b, htr168a, htr235c, htr256c, htr267a, htr678c])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr013b, htr036a, htr136a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc345xy, htr023c, htr036c, htr067a, htr134b, htr146b, htr167a, htr235a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc456zy, htr067a, htr068a, htr467a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          rcases m.htr 2 3 6 (by decide) (by decide) with
            ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
          ·
            linarith only [hlam, htr123c, htr136a, htr236a]
          ·
            linarith only [hlam, hc345xy, htr134b, htr146b, htr167a, htr235a, htr236c, htr267a]
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
          linarith only [hlam, hc126xy, htr012c, htr016a, htr023a, htr123a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc127xy, htr012c, htr017a, htr023a, htr123a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc128xy, htr012c, htr018a, htr023a, htr123a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
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
          linarith only [hlam, htr025a, htr026a, htr256c])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr025a, htr027a, htr257c])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr025a, htr028a, htr258c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, htr023b, htr034a, htr234a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc012zy, htr023c, htr035a, htr123a, htr235a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr025b, htr056a, htr257a, htr567b])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr025b, htr057a, htr257a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr025b, htr058a, htr258a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc012zy, hc567yz, htr024b, htr025a, htr047b, htr078a, htr124a, htr257a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr134a, htr134b, htr134c, _, _⟩
          linarith only [hlam, hc012zy, htr023a, htr123b, htr134a, htr234a])
        obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc012zy, hc345xy, htr025a, htr123a, htr134a, htr135b, htr156a, htr235a, htr257a, htr567b])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc012zy, hc345xy, htr025a, htr123a, htr134a, htr135b, htr157a, htr235a, htr257a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc012zy, hc345xy, htr025a, htr123a, htr134a, htr135b, htr158a, htr235a, htr258a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc012zy, hc456zy, htr025a, htr124a, htr126c, htr167a, htr246a, htr256c, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc012zy, hc456zy, htr025a, htr124a, htr126c, htr168a, htr246a, htr256c, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc012zy, htr025a, htr124b, htr146b, htr167a, htr256c, htr267a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc012zy, htr026c, htr067a, htr126a, htr267a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc012zy, hc567yz, htr025a, htr067a, htr068a, htr124b, htr146b, htr168a, htr257a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr026b, htr068a, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc012zy, htr027c, htr078a, htr127a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc012zy, htr025a, htr124b, htr147b, htr178a, htr257c, htr278a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc012zy, hc346xy, htr023a, htr126a, htr234a, htr267a, htr367a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc012zy, hc567yz, htr023b, htr025a, htr036a, htr123a, htr257a, htr367a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc345xy, htr035a, htr036a, htr134a, htr136a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr123c, htr136a, htr236a])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc012zy, htr023a, htr024b, htr046b, htr068a, htr123c, htr124a, htr136a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc012zy, hc357yx, htr025a, htr123a, htr235a, htr257c, htr278a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc012zy, hc478zy, htr023a, htr123c, htr124a, htr137a, htr248a, htr378a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc345xy, htr035a, htr037a, htr134a, htr137a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr023b, htr037a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          linarith only [hlam, hc012zy, hc567yz, htr025a, htr124a, htr246a, htr257a, htr467a]
        ·
          linarith only [hlam, hc346yz, htr136a, htr137a, htr367c, htr467a]
    ·
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc012zy, hc468zy, htr025a, htr124a, htr248a, htr257a, htr567b, htr568a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr023a, htr023b, htr023c, _, _⟩
        linarith only [hlam, hc345xy, htr023a, htr025a, htr234a, htr235c])
      obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc345xy, htr023a, htr024a, htr234b, htr235a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr024a, htr026a, htr246b])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr024a, htr027a, htr247b])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr024a, htr028a, htr248b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr023c, htr035a, htr235a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc026xy, hc468zy, htr024a, htr067a, htr248a, htr567a, htr568a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc067yz, htr078a, htr567a, htr568a, htr678b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc012yx, hc468zy, htr013a, htr024a, htr136a, htr248a, htr356b, htr568a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc012yx, hc468zy, htr013a, htr024a, htr137a, htr248a, htr357b, htr567b, htr568a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc126xy, hc468zy, htr124a, htr167a, htr248a, htr567a, htr568a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc167yz, htr178a, htr567a, htr568a, htr678b])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr256b, htr268a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr257b, htr278a, htr567b, htr568a, htr678b])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr356b, htr368a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr357b, htr378a, htr567b, htr568a, htr678b])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr456b, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      rcases m.htr 1 3 4 (by decide) (by decide) with
        ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hc123yz, htr013a, htr014a, htr134c, htr234a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr134a, htr138a, htr348b])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc345xy, hc678yx, htr023c, htr036a, htr235a, htr346a, htr356b, htr467a, htr568a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd13a, hd67b, htr034a, htr036a, htr134a, htr346c, htr467a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc678yx, htr034a, htr037a, htr234b, htr246a, htr357b, htr467a, htr567b, htr568a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr034a, htr038a, htr348b])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc025xy, hc678yx, htr024a, htr056a, htr246a, htr467a, htr568a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc125xy, hc678yx, htr124a, htr156a, htr246a, htr467a, htr568a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc145yz, htr015a, htr016a, htr156c, htr456a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc135yz, hc137xy, htr015a, htr017a, htr134a, htr234a, htr235a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr017a, htr018a, htr178c])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr015b, htr058a, htr158a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          rcases m.htr 1 6 8 (by decide) (by decide) with
            ⟨htr168a, htr168b, htr168c, _, _⟩ | ⟨htr168a, htr168b, htr168c, _, _⟩
          ·
            linarith only [hlam, hc145yz, htr156b, htr168a, htr456a, htr568a]
          ·
            linarith only [hlam, hc012yx, hc678yx, htr016a, htr024a, htr168a, htr246a, htr467a]
        ·
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr167a, htr467a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc146yz, htr016a, htr017a, htr167c, htr467a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc125xy, hc478zy, htr015a, htr017a, htr124a, htr178a, htr248a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr017a, htr018a, htr178c])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc678yx, htr056a, htr057a, htr567c, htr568a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr056a, htr058a, htr568c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr056b, htr068a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          rcases m.htr 1 5 6 (by decide) (by decide) with
            ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
          ·
            linarith only [hlam, hc145yz, htr156a, htr456c, htr467a, htr567a]
          ·
            linarith only [hlam, hc012yx, hc468zy, htr015a, htr024a, htr156a, htr248a, htr568a]
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, htr013a, htr014a, htr134c])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc345xy, htr013a, htr015a, htr125c, htr134a, htr235c])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc345xy, hc678yx, htr013a, htr016a, htr134a, htr167a, htr356a, htr568a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc345xy, htr013a, htr017a, htr127c, htr134a, htr235c, htr257c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr017a, htr018a, htr178c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, htr013b, htr034a, htr134a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc345xy, htr023c, htr036a, htr134a, htr136a, htr235a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc345xy, htr023c, htr037a, htr134a, htr137a, htr235a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc345xy, htr013b, htr035b, htr056a, htr134a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc345xy, hc678yx, htr056a, htr057a, htr134a, htr136b, htr167a, htr357a, htr568a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr056a, htr058a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        rcases m.htr 1 5 6 (by decide) (by decide) with
          ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
        ·
          linarith only [hlam, hc345xy, htr134a, htr135b, htr156a, htr356a]
        ·
          linarith only [hlam, hc012yx, hc468zy, htr015a, htr024a, htr156a, htr248a, htr568a]

theorem shard_194 {lam p : ℝ} (m : NineModel lam p)
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
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False :=
  proof_shard_194 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c

#print axioms shard_194
end Jsp404.NoSatNineDBMTerminal
