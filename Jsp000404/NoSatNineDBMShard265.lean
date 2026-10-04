import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_265 {lam p : ℝ} (m : NineModel lam p)
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
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348b : m.d 3 4 < m.d 3 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr248b : m.d 2 4 < m.d 2 8)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr156b : m.d 1 5 < m.d 1 6)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
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
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, hc017yx, hd34a, hd56b, htr012a, htr078a, htr123a, htr234a, htr567a, htr678a])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr567b, htr678a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd34a, hd56b, htr347a, htr478a, htr567a, htr678a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, htr567a, htr568a, htr678c])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, htr567b, htr578a, htr678a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  rcases m.htr 2 3 5 (by decide) (by decide) with
    ⟨htr235a, htr235b, htr235c, _, _⟩ | ⟨htr235a, htr235b, htr235c, _, _⟩
  ·
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hc034zy, htr045a, htr234a, htr235a, htr345c])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr045a, htr046a, htr456b])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr045a, htr047a, htr347a, htr456a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr045a, htr048a, htr348a, htr456a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045c, htr056a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr045c, htr057a, htr234a, htr235b, htr257a, htr456a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, hd01b, hd34a, htr012a, htr123c, htr135a, htr234a, htr235a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr135a, htr136a, htr356b])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr014b, htr047a, htr147a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, htr014b, htr048a, htr148a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr015b, htr057a, htr157a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr135b, htr137c, htr157b])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr125b, htr157b, htr178a, htr234a, htr235b, htr567a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, htr235a, htr236a, htr356b])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc346xy, htr012b, htr026a, htr123a, htr234a, htr236c])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, hc346xy, htr123a, htr126a, htr234a, htr236c])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, htr123b, htr137a, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc347xy, htr012b, htr027a, htr123a, htr234a, htr237c])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr027c, htr028b, htr078c])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc347xy, htr123a, htr127a, htr234a, htr237c])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hd02b, hd34a, htr028a, htr123a, htr128a, htr234a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc568yx, hd01b, hd34a, htr012a, htr125a, htr234a, htr235a, htr258a, htr345c, htr456a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr045c, htr058a, htr234a, htr235b, htr258a, htr456a])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, htr015b, htr058a, htr158a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr135b, htr138c, htr158b])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd01b, hd34a, htr016a, htr167a, htr234a, htr235b, htr256b, htr267a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr234a, htr235b, htr257b, htr278a, htr567a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hc578zy, hd01b, hd34a, htr012a, htr035b, htr058a, htr127a, htr234a, htr235a, htr278a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr035a, htr036a, htr356b])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc345xy, htr035a, htr037a, htr123b, htr137a, htr234a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc345xy, htr035a, htr038a, htr123b, htr138a, htr234a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc346xy, htr036c, htr067a, htr234a, htr235b, htr256b, htr267a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr257a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    rcases m.htr 3 5 8 (by decide) (by decide) with
      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
    ·
      linarith only [hlam, hc578zy, hd01b, hd34a, htr012a, htr127a, htr234a, htr235a, htr278a, htr358a]
    ·
      linarith only [hlam, hc345xy, htr234a, htr235b, htr258a, htr358a]
  ·
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr013b, htr035a, htr123b, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc035zy, hd01b, hd34a, htr012a, htr056a, htr123a, htr235a, htr345a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, htr123b, htr135a, htr235a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr235b, htr257a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd01b, hd58a, htr012a, htr123a, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hd01b, hd35a, htr012a, htr125a, htr258a, htr358a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr056a, htr057a, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015b, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr012b, htr026a, htr123a, htr234a, htr246c, htr467a, htr567a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr012b, htr027a, htr123a, htr234a, htr247c, htr467c, htr567a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr012b, htr028a, htr123a, htr234a, htr248c, htr467c, htr478c, htr567a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr013b, htr036a, htr123b, htr234a, htr346c, htr467a, htr567a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc356yz, htr036a, htr037a, htr347c, htr467c, htr567a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc356yz, htr036a, htr038a, htr348c, htr467c, htr478c, htr567a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc014yx, hd34a, hd56b, htr012a, htr045a, htr123a, htr234a, htr456b, htr467a, htr567a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr045a, htr046a, htr345a, htr467a, htr567a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr045a, htr047a, htr345a, htr467c, htr567a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr047a, htr048a, htr478c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc034zy, htr046c, htr067a, htr346a, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr123a, htr126a, htr234a, htr246c, htr467a, htr567a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc034zy, htr047a, htr123a, htr127a, htr234a, htr247c])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc034zy, htr047a, htr123a, htr128a, htr234a, htr248c, htr478c])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr123b, htr136a, htr234a, htr346c, htr467a, htr567a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc034zy, hc356yz, htr047a, htr136a, htr137a, htr346a, htr347c, htr467a, htr567a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc034zy, hc356yz, htr047a, htr136a, htr138a, htr346a, htr348c, htr467a, htr478c, htr567a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015b, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr016b, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc034zy, hc156yz, htr047a, htr167b, htr178a, htr346a, htr467a, htr478a, htr567a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        rcases m.htr 2 3 6 (by decide) (by decide) with
          ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
        ·
          linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr346c, htr467a, htr567a]
        ·
          linarith only [hlam, hc356yz, hd01b, hd34a, htr012a, htr123a, htr236a, htr346a, htr467a, htr567a]
      ·
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc034zy, hd01b, hd78a, htr012a, htr046a, htr123a, htr234a, htr467a, htr678a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr014b, htr046a, htr146a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr467a, htr468a, htr678c])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        rcases m.htr 2 3 6 (by decide) (by decide) with
          ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc346xy, htr012b, htr026a, htr123a, htr234a, htr236c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, hc346xy, htr123a, htr126a, htr234a, htr236c])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hd01b, hd34a, htr012a, htr123c, htr136a, htr234a, htr236a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc346xy, htr134c, htr136a, htr145a, htr345a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457b])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc346xy, htr134c, htr136a, htr148a, htr348a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc356xy, htr135c, htr136a, htr158a, htr358a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr012b, htr027a, htr123a, htr234a, htr267c, htr567a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr027c, htr028b, htr078c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc246yz, htr046a, htr047a, htr267a, htr467b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr123a, htr127a, htr234a, htr267c, htr567a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hd02b, hd34a, htr028a, htr123a, htr128a, htr234a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hd01b, hd34a, htr016a, htr167a, htr234a, htr236b, htr267a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr136b, htr137c, htr167b])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc256yz, htr127b, htr178a, htr267b, htr567a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc256yz, htr267b, htr278a, htr567a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a]
          ·
            linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a]
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr012b, htr026a, htr123a, htr236c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc356yz, htr012b, htr027a, htr123a, htr236a, htr257c, htr567c])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc356yz, htr012b, htr028a, htr123a, htr236a, htr258c, htr568c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr013b, htr036a, htr123b, htr236a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          rcases m.htr 0 4 5 (by decide) (by decide) with
            ⟨htr045a, htr045b, htr045c, _, _⟩ | ⟨htr045a, htr045b, htr045c, _, _⟩
          ·
            linarith only [hlam, hc014yx, hc356yz, htr012a, htr045a, htr123a, htr236a, htr456a]
          ·
            linarith only [hlam, hc346yz, hd01b, hd34a, htr012a, htr045a, htr046a, htr123a, htr236a, htr345a]
    ·
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc256xy, hd34a, hd56b, htr012b, htr026a, htr123a, htr234a, htr257a, htr456a, htr457a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr012b, htr027a, htr123a, htr234a, htr257c, htr456a, htr457a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr012b, htr028a, htr123a, htr234a, htr258c, htr456a, htr457a, htr578c])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr013b, htr037a, htr123b, htr234a, htr357c, htr456a, htr457a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr013b, htr038a, htr123b, htr234a, htr358c, htr456a, htr457a, htr578c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc024zy, htr045a, htr245b, htr257a, htr457a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr045a, htr046a, htr456b])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr045a, htr047a, htr347a, htr456a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr045a, htr048a, htr348a, htr456a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc015yx, hd34a, hd56b, htr012a, htr057a, htr123a, htr234a, htr456a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc346xy, htr035c, htr036a, htr057a, htr234b, htr245b, htr257a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057a, htr058a, htr578c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hd02b, hd34a, htr026a, htr123a, htr126a, htr234a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr123a, htr127a, htr234a, htr257c, htr456a, htr457a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr123a, htr128a, htr234a, htr258c, htr456a, htr457a, htr578c])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr123b, htr137a, htr234a, htr357c, htr456a, htr457a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr123b, htr138a, htr234a, htr358c, htr456a, htr457a, htr578c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr014b, htr045a, htr145a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014b, htr047a, htr147a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc156yz, htr167a, htr456a, htr457a, htr567b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr167a, htr168a, htr678c])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr167b, htr178a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc356yz, hd01b, hd78a, htr012a, htr123a, htr236a, htr456a, htr457a, htr567b, htr678a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hd01b, hd34a, htr012a, htr123c, htr136a, htr234a, htr236a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc346xy, htr135c, htr136a, htr157a, htr234b, htr245b, htr257a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc568yx, htr157a, htr158a, htr456a, htr457a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc346xy, htr136a, htr137a, htr234a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc346xy, htr136a, htr138a, htr234a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      rcases m.htr 2 6 7 (by decide) (by decide) with
        ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
      ·
        linarith only [hlam, hc256yz, htr267a, htr456a, htr457a, htr567b]
      ·
        linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]

theorem shard_265 {lam p : ℝ} (m : NineModel lam p)
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
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348b : m.d 3 4 < m.d 3 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr248b : m.d 2 4 < m.d 2 8)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr156b : m.d 1 5 < m.d 1 6)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    : False :=
  proof_shard_265 m htr012a htr012b htr012c htr123a htr123b htr123c htr013a htr013b htr013c htr023a htr023b htr023c htr234a htr234b htr234c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr024a htr024b htr024c htr034a htr034b htr034c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr245a htr245b htr245c htr346a htr346b htr346c htr246a htr246b htr246c htr347a htr347b htr347c htr247a htr247b htr247c htr348a htr348b htr348c htr248a htr248b htr248c htr456a htr456b htr456c htr025a htr025b htr025c htr125a htr125b htr125c htr156a htr156b htr156c htr256a htr256b htr256c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c

#print axioms shard_265
end Jsp404.NoSatNineDBMTerminal
