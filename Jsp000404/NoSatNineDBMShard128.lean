import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_128 {lam p : ℝ} (m : NineModel lam p)
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
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr467a : m.d 6 7 + lam ≤ m.d 4 6)
    (htr467b : m.d 6 7 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 4 6)
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
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < (7/2 : ℝ)*lam := by
    linarith only [hd06braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < (7/2 : ℝ)*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd28a, hd28braw⟩ := m.hrange 2 8 (by decide)
  have hd28b : m.d 2 8 < (7/2 : ℝ)*lam := by
    linarith only [hd28braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc034zy, htr045a, htr234a, htr235a, htr345c])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hc345xy, htr123a, htr125a, htr234a, htr235c])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc134zy, htr145a, htr234a, htr235a, htr345c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc345xy, htr234c, htr235a, htr246a, htr346a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457yx, htr234a, htr235a, htr345c, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc345xy, htr234c, htr235a, htr247a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458yx, htr234a, htr235a, htr345c, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc345xy, htr234c, htr235a, htr248a, htr348a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd34a, hd45b, htr234a, htr235a, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc267zy, hc345xy, htr123a, htr127a, htr234a, htr356a, htr567a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc345xy, htr125b, htr156a, htr234a, htr235b, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, hd12b, hd67a, htr012a, htr015a, htr156a, htr567a])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, htr125c, htr126b, htr156c])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr156a, htr157a, htr567c])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, htr156b, htr167a, htr567a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hc012yz, hc467zy, htr024a, htr125a, htr247a, htr256a, htr567a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr023a, htr023b, htr023c, _, _⟩
    linarith only [hlam, hc345xy, htr023a, htr024a, htr234b, htr235a])
  obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
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
    linarith only [hlam, hc267zy, htr025a, htr027a, htr256a, htr567a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hd28b, hd67a, htr025a, htr028a, htr256a, htr567a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, htr023b, htr034a, htr234a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr025b, htr056a, htr256a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr025b, htr057a, htr256a, htr567c])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr026b, htr067a, htr256b, htr567a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, htr012c, htr028a, htr128a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, hc012xy, hc367zy, htr013a, htr025a, htr137a, htr256a, htr567a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr256a, htr257a, htr567c])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, htr256b, htr267a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr356a, htr357a, htr567c])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr356b, htr367a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd12b, hd67a, htr125a, htr256a, htr567c, htr578a, htr678a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc678xy, htr025b, htr058a, htr256a, htr567a, htr568c])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc067zy, htr078a, htr567a, htr568a, htr678c])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, htr015c, htr058a, htr158a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc167zy, htr178a, htr567a, htr568a, htr678c])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc678xy, htr256a, htr258a, htr567a, htr568c])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr567a, htr568a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, htr235c, htr258a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, htr137b, htr178a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr045c, htr058a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    rcases m.htr 0 1 4 (by decide) (by decide) with
      ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr014a, htr016a, htr145a, htr156b, htr567a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127yx, hd45b, hd67a, htr014a, htr017a, htr125a, htr145a, htr256a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr017a, htr018a, htr178b])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc012xy, hc467zy, htr014a, htr025a, htr147a, htr256a, htr567a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc134zy, htr023b, htr037a, htr147a, htr234a, htr347c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc024yx, hd45b, hd67a, htr025a, htr047a, htr145a, htr147a, htr256a, htr567a])
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
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, htr013c, htr035a, htr135a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc012xy, hc678xy, htr016a, htr025a, htr168a, htr256a, htr567a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr145a, htr146c, htr168a, htr567a, htr568a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr146a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hd16b, hd34a, htr046b, htr047a, htr068a, htr168a, htr347a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd03b, hd67a, htr035a, htr235a, htr236a, htr356b, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc134zy, htr147a, htr234a, htr237a, htr347c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hd03b, hd67a, htr035a, htr235a, htr238a, htr358b, htr567a, htr568b])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc034zy, htr048a, htr234a, htr238a, htr348c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc457yx, htr047a, htr048a, htr145a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      rcases m.htr 3 6 8 (by decide) (by decide) with
        ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
      ·
        linarith only [hlam, hd16b, hd34a, htr168a, htr234a, htr236a, htr368a]
      ·
        linarith only [hlam, hd03b, hd67a, htr035a, htr356c, htr368a, htr567a, htr568a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc124yx, hc167zy, htr014a, htr017a, htr125a, htr256a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc345xy, htr013a, htr014a, htr124b, htr135a, htr234b])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc134yx, htr013b, htr014a, htr035a, htr135a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr035a, htr036a, htr356c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr035a, htr038a, htr358c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr135a, htr136a, htr356c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr135a, htr138a, htr358c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr012a, htr014a, htr146a, htr456b, htr567a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc124yx, htr012a, htr014c, htr046a, htr146a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr147a, htr347a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047a, htr048a, htr478b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr147a, htr148a, htr478b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr135a, htr235a, htr236a, htr356b, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr016a, htr136b, htr234a, htr236a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc345xy, hc678xy, htr036b, htr068a, htr234a, htr236a, htr356a, htr567a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr016c, htr068a, htr168a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr012a, htr018a, htr168b, htr567a, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr017a, htr137b, htr234a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr135a, htr235a, htr238a, htr358b, htr567a, htr568b])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      rcases m.htr 3 6 8 (by decide) (by decide) with
        ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
      ·
        linarith only [hlam, hd06b, hd34a, htr068a, htr234a, htr236a, htr368a]
      ·
        linarith only [hlam, hd13b, hd67a, htr135a, htr356c, htr368a, htr567a, htr568a]
  ·
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, htr025b, htr058a, htr256a, htr568c])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr026b, htr068a, htr256b, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hc012xy, hc368zy, htr013a, htr025a, htr138a, htr256a, htr568a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, htr125b, htr158a, htr256a, htr568c])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr156b, htr168a, htr568a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, htr256a, htr258a, htr568c])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr256b, htr268a, htr568a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, htr235c, htr256a, htr358a, htr568c])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, htr356b, htr368a, htr568a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr345c, htr356a, htr458a, htr568c])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr456b, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    rcases m.htr 0 1 4 (by decide) (by decide) with
      ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr014a, htr016a, htr145a, htr156b, htr567a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127yx, hd45b, hd67a, htr014a, htr017a, htr125a, htr145a, htr256a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128yx, hd45b, hd67a, htr014a, htr018a, htr125a, htr145a, htr256a, htr567a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc012xy, hc467zy, htr014a, htr025a, htr147a, htr256a, htr567a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc134zy, htr023b, htr037a, htr147a, htr234a, htr347c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc024yx, hd45b, hd67a, htr025a, htr047a, htr145a, htr147a, htr256a, htr567a])
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
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, htr013c, htr035a, htr135a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc012xy, hc678yz, htr017a, htr025a, htr178a, htr256a, htr568a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc457yx, htr047b, htr078a, htr145a, htr147c, htr178a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd03b, hd67a, htr035a, htr235a, htr236a, htr356b, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc034zy, htr046a, htr234a, htr236a, htr346c])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hc457yx, htr046a, htr047a, htr145a, htr146a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc134zy, htr147a, htr234a, htr237a, htr347c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc034zy, htr048a, htr234a, htr238a, htr348c])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr145a, htr147a, htr247c, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr237b, htr278a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        linarith only [hlam, hc457yx, htr145a, htr147c, htr178a, htr478a]
      ·
        linarith only [hlam, hd45b, hd67a, htr145a, htr147a, htr478a, htr678a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc124yx, hc167zy, htr014a, htr017a, htr125a, htr256a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc124yx, hc168zy, htr014a, htr018a, htr125a, htr256a, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc345xy, htr013a, htr014a, htr124b, htr135a, htr234b])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc134yx, htr013b, htr014a, htr035a, htr135a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr035a, htr036a, htr356c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr135a, htr136a, htr356c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr012a, htr014a, htr146a, htr456b, htr567a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc124yx, htr012a, htr014c, htr046a, htr146a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr147a, htr347a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc345xy, hc467zy, htr047a, htr048a, htr348a, htr356a, htr567a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr135a, htr235a, htr236a, htr356b, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr016a, htr136b, htr234a, htr236a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr017a, htr137b, htr234a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr018a, htr138b, htr234a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127b, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc137yx, htr135a, htr178a, htr235a, htr237a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        linarith only [hlam, hc124yx, hc678yz, htr125a, htr147a, htr256a, htr478a, htr568a]
      ·
        linarith only [hlam, hc127yx, hc467zy, htr125a, htr178a, htr256a, htr478a, htr567a]

theorem shard_128 {lam p : ℝ} (m : NineModel lam p)
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
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr467a : m.d 6 7 + lam ≤ m.d 4 6)
    (htr467b : m.d 6 7 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 4 6)
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
  proof_shard_128 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr245a htr245b htr245c htr346a htr346b htr346c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c htr235a htr235b htr235c

#print axioms shard_128
end Jsp404.NoSatNineDBMTerminal
