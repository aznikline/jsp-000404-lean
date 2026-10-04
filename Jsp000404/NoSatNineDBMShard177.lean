import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_177 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr578a : m.d 7 8 + lam ≤ m.d 5 7)
    (htr578b : m.d 7 8 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 5 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr478a : m.d 7 8 + lam ≤ m.d 4 7)
    (htr478b : m.d 7 8 < m.d 4 8)
    (htr478c : m.d 4 8 < m.d 4 7)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd02a := (m.hrange 0 2 (by decide)).1
  have hd04a := (m.hrange 0 4 (by decide)).1
  obtain ⟨hd05a, hd05braw⟩ := m.hrange 0 5 (by decide)
  have hd05b : m.d 0 5 < (7/2 : ℝ)*lam := by
    linarith only [hd05braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < (7/2 : ℝ)*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd18a, hd18braw⟩ := m.hrange 1 8 (by decide)
  have hd18b : m.d 1 8 < (7/2 : ℝ)*lam := by
    linarith only [hd18braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd28a := (m.hrange 2 8 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd38a := (m.hrange 3 8 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc057xy, hc057yx, hc057yz, hc057zy⟩ := endpoint_caps m 0 5 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc148xy, hc148yx, hc148yz, hc148zy⟩ := endpoint_caps m 1 4 8 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc158xy, hc158yx, hc158yz, hc158zy⟩ := endpoint_caps m 1 5 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  rcases m.htr 1 3 4 (by decide) (by decide) with
    ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd12a, hd56b, htr012a, htr014a, htr134c, htr345a, htr456a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, hc123yz, htr023a, htr024a, htr134a, htr234b])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hc123yz, htr023a, htr025a, htr134a, htr235b, htr345b])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc123yz, hc256yz, htr023a, htr026a, htr134a, htr345a, htr456a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc123yz, hc257yz, htr023a, htr027a, htr134a, htr345a, htr457a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hc123yz, htr024c, htr045a, htr134a, htr234c, htr345a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr045a, htr046a, htr456b])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, htr045a, htr047a, htr457b])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045c, htr056a, htr457a, htr567c])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr045c, htr057a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc057yz, hd13a, hd56b, htr078a, htr134a, htr345a, htr457a, htr567a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
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
      linarith only [hlam, htr012b, htr027a, htr127a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hc238yx, htr123b, htr128a, htr134a, htr234a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hd12a, hd56b, htr024b, htr028a, htr045a, htr128a, htr456a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
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
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr134a, htr137a, htr347b])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hd38a, hd56b, htr134a, htr138a, htr345a, htr456a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr134c, htr145a, htr345a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134c, htr146a, htr345a, htr456b])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr134c, htr147a, htr345a, htr457b])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr135c, htr156a, htr235a, htr345a, htr457a, htr567c])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr135c, htr157a, htr235a, htr345a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc123yz, hc568yx, htr134a, htr135c, htr158a, htr235a, htr345a, htr456a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, htr145b, htr148c, htr158b])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hd14a, hd56b, htr045a, htr048a, htr148a, htr456a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc157yz, hd13a, hd56b, htr134a, htr178a, htr345a, htr457a, htr567a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr234c, htr245a, htr345a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr245a, htr246a, htr456b])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr245a, htr247a, htr457b])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, hd14a, hd56b, htr148a, htr245a, htr248a, htr456a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr245c, htr256a, htr457a, htr567c])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr245c, htr257a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, htr027c, htr078a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, htr234b, htr248a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr158a, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc123yz, htr025c, htr058a, htr134a, htr235c, htr345b, htr358a])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc123yz, htr134a, htr235c, htr258a, htr345b, htr358a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, htr137c, htr178a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr134a, htr345b, htr358a, htr456a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc012yx, hc578zy, htr017a, htr024a, htr178a, htr245a, htr458a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc137xy, hc156yz, htr016a, htr017a, htr134a, htr345a, htr456a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc137xy, hc158yz, htr017a, htr018a, htr134a, htr345a, htr458a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc137xy, htr013c, htr017a, htr034a, htr134a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr034a, htr035a, htr345b])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc026xy, hc578zy, htr024a, htr067a, htr245a, htr458a, htr678a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc568zy, hd13a, hd56b, htr067a, htr068a, htr134a, htr345a, htr458a, htr567a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 1 6 7 (by decide) (by decide) with
      ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
    ·
      linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr167a, htr567a]
    ·
      linarith only [hlam, hc126xy, htr012a, htr016b, htr067a, htr167a]
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, htr013a, htr014a, htr134c])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr013b, htr034a, htr134a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125xy, hd34a, hd56b, htr013a, htr015a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc126xy, hd34a, hd56b, htr013a, htr016a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127xy, hd34a, hd56b, htr013a, htr017a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128xy, hd34a, hd56b, htr013a, htr018a, htr124a, htr134a, htr245a, htr456a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hd05b, hd12a, htr056a, htr124a, htr245a, htr457a, htr567c])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd12a, hd56b, htr056a, htr057a, htr124a, htr245a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc057yz, hd12a, hd56b, htr078a, htr124a, htr245a, htr457a, htr567a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr124a, htr125a, htr245b])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc256yz, htr124a, htr126a, htr245a, htr456a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc257yz, htr124a, htr127a, htr245a, htr457a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hd28a, hd56b, htr124a, htr128a, htr245a, htr456a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr124c, htr145a, htr245a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124c, htr146a, htr245a, htr456b])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr124c, htr147a, htr245a, htr457b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015b, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015b, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc157yz, hd12a, hd56b, htr124a, htr178a, htr245a, htr457a, htr567a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456b])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr245a, htr247a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, htr245c, htr256a, htr457a, htr567c])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245c, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127c, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc357yz, hd12a, hd56b, htr124a, htr245a, htr378a, htr457a, htr567a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd12a, hd56b, htr124a, htr245a, htr456b, htr467a, htr567a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr467a, htr468a, htr678c])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      rcases m.htr 2 3 6 (by decide) (by decide) with
        ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
      ·
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc346xy, htr023a, htr024a, htr234b, htr236a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, htr024a, htr025a, htr245b])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, htr023a, htr026a, htr236b])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr024a, htr027a, htr247b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hd12a, hd56b, htr024a, htr028a, htr128a, htr245a, htr456a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc346xy, htr013b, htr035a, htr134a, htr235a, htr236a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, htr023c, htr036a, htr236a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, htr024c, htr045a, htr245a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hc346xy, htr134a, htr135a, htr235a, htr236a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr123c, htr136a, htr236a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc012yx, hc357yz, htr013a, htr024a, htr137a, htr245a, htr457a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc346xy, htr023c, htr037a, htr134a, htr137a, htr236a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc012yx, hc568yx, htr015a, htr024a, htr158a, htr245a, htr456a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc346xy, htr025c, htr058a, htr134b, htr145b, htr158a, htr235c, htr236a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045b, htr048c, htr058b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc012yx, hd56b, hd78a, htr016a, htr024a, htr167a, htr245a, htr456a, htr678a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc346xy, htr026c, htr067a, htr134a, htr136b, htr167a, htr236c])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, hc346xy, htr134a, htr137a, htr236a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hd04a, hd56b, htr048a, htr245a, htr248a, htr456a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc346xy, htr134b, htr145b, htr158a, htr235c, htr236a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc346xy, htr134a, htr136b, htr167a, htr236c, htr267a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc012yx, htr013a, htr024a, htr134a, htr248a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc012yx, htr013a, htr024a, htr135a, htr245b, htr258a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 3 6 7 (by decide) (by decide) with
          ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd56b, htr123a, htr236a, htr367a, htr567a]
        ·
          linarith only [hlam, hc346xy, htr134a, htr136b, htr167a, htr367a]
      ·
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr024a, htr024b, htr024c, _, _⟩
            linarith only [hlam, hc012yx, hc578zy, htr017a, htr024a, htr178a, htr245a, htr458a])
          obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hd12a, hd56b, htr024a, htr025a, htr124a, htr245c, htr456a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc012zy, hc578zy, htr027a, htr124a, htr127c, htr178a, htr245a, htr458a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc234yx, htr023b, htr024a, htr036a, htr236a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc012zy, htr024c, htr045a, htr124a, htr245a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc578zy, htr045a, htr046a, htr458a, htr467a, htr678a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr045a, htr048a, htr458b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr045c, htr058a, htr458a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hc123yz, htr023a, htr025a, htr135a, htr235b])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc123xy, hc578zy, htr124a, htr137a, htr245a, htr378a, htr458a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr124c, htr148a, htr245a, htr458b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc012zy, htr025a, htr124a, htr125c, htr158a, htr245a, htr458a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc126xy, hc578zy, htr124a, htr167a, htr245a, htr458a, htr678a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc568zy, hd12a, hd56b, htr124a, htr167a, htr168a, htr245a, htr458a, htr567a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc347xy, htr023a, htr024a, htr234b, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc234yx, htr023b, htr024a, htr037a, htr237a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr037a, htr038a, htr378c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc234yx, hc356yz, htr136a, htr137a, htr237a, htr245a, htr456a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc123yz, htr023a, htr026a, htr136a, htr236b])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr036b, htr067a, htr134a, htr136a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc234yx, hc358yz, htr137a, htr138a, htr237a, htr245a, htr458a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, htr237a, htr238a, htr378c])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc123yz, htr023a, htr028a, htr138a, htr238b])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr245a, htr248a, htr458b])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, htr026c, htr067a, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr367a, htr567a]
          ·
            linarith only [hlam, hc346xy, htr134a, htr136b, htr168a, htr367a, htr678c]
        ·
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc056yz, htr068a, htr456a, htr458a, htr568b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc568yx, htr124c, htr148a, htr245a, htr456a, htr458b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc156yz, htr168a, htr456a, htr458a, htr568b])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc568yx, htr245a, htr248a, htr456a, htr458b])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hd12a, hd56b, htr124a, htr245b, htr258a, htr456a, htr458a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc012zy, hc568yx, htr025a, htr124a, htr245a, htr258a, htr456a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr024a, htr024b, htr024c, _, _⟩
            linarith only [hlam, hd12a, hd56b, htr024a, htr025a, htr124a, htr245c, htr456a])
          obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc568yx, htr024a, htr026a, htr245a, htr256b, htr258a, htr456a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc568yx, htr024a, htr027a, htr245a, htr257b, htr258a, htr456a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr024a, htr028a, htr248b])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, htr024c, htr045a, htr248a, htr458c])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr024c, htr048a, htr248a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc012yx, hc356yz, htr013a, htr024a, htr136a, htr245a, htr456a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc023xy, hd34a, hd56b, htr024a, htr036a, htr134a, htr136a, htr245a, htr456a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr036a, htr037a, htr236a, htr378a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr013b, htr037a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc012yx, hc568yx, htr015a, htr024a, htr158a, htr245a, htr456a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr134a, htr135b, htr158a, htr456a, htr458a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, htr013b, htr035a, htr135a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc346xy, htr035c, htr036a, htr058a, htr134b, htr145b, htr158a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc012yx, hd56b, hd78a, htr016a, htr024a, htr167a, htr245a, htr456a, htr678a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd23b, hd68a, htr036c, htr067a, htr167a, htr168a, htr236a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc347xy, htr134a, htr136a, htr236a, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, htr237a, htr238a, htr378c])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc568yx, htr256b, htr258a, htr267a, htr567a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc012yx, htr013a, htr024a, htr134a, htr248a, htr348a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr135b, htr158a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr013b, htr038a, htr134a, htr358c, htr456a, htr458a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc346xy, htr036a, htr038a, htr134a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr367a, htr567a]
          ·
            linarith only [hlam, hd23b, hd68a, htr167a, htr168a, htr236a, htr367a]
    ·
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr245a, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc234zy, htr024a, htr025a, htr245b, htr345a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234zy, htr013b, htr035a, htr134a, htr245a, htr345c])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, htr013c, htr015b, htr035c])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr056a, htr245c, htr345a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr025b, htr026c, htr056b])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr057a, htr245c, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr025b, htr027c, htr057b])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr012b, htr025a, htr125a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr012b, htr026a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, htr012b, htr027a, htr127a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc234zy, htr134a, htr135a, htr245a, htr345c])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr015b, htr056a, htr156a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015b, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc346xy, htr234c, htr236a, htr245a, htr345a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc347xy, htr234c, htr237a, htr245a, htr345a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc348xy, htr234c, htr238a, htr245a, htr345a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc234zy, htr245c, htr257a, htr345a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd02a, hd56b, htr027a, htr278a, htr567a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc012yx, hc568yx, htr013a, htr025a, htr135a, htr256a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr345b, htr348c, htr358b])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc234zy, htr245a, htr345b, htr358a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr058a, htr245c, htr345a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr025b, htr028c, htr058b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr012b, htr028a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015b, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc234zy, htr245c, htr258a, htr345a, htr458a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc012yx, hc578zy, htr013a, htr025a, htr134c, htr147a, htr258a, htr478a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr013a, htr017a, htr134a, htr147c, htr467c, htr567a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr013b, htr036a, htr134a, htr346c, htr467a, htr567a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr013c, htr016b, htr036c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc356yz, htr036a, htr037a, htr347c, htr467c, htr567a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc356yz, htr036a, htr038a, htr348c, htr467c, htr478c, htr567a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr013c, htr018b, htr038c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr346c, htr467a, htr567a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc014yx, hc356yz, htr013a, htr045a, htr136a, htr456b, htr467a, htr567a])
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
          linarith only [hlam, hc034zy, htr046c, htr067a, htr345a, htr456b, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr047b, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc034zy, hc356yz, htr047a, htr136a, htr137a, htr345a, htr347c, htr456b, htr467a, htr567a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc034zy, hc356yz, htr047a, htr136a, htr138a, htr345a, htr348c, htr456b, htr467a, htr478c, htr567a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc034zy, htr047a, htr145a, htr147a, htr345a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr145a, htr146a, htr456b])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr145a, htr148a, htr458b])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr016b, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc034zy, hc156yz, htr047a, htr167b, htr178a, htr345a, htr456b, htr467a, htr478a, htr567a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr024c, htr046a, htr246a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr024c, htr047a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        rcases m.htr 2 6 7 (by decide) (by decide) with
          ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
        ·
          linarith only [hlam, hc012yx, hc356yz, htr013a, htr026a, htr136a, htr267a, htr567a]
        ·
          linarith only [hlam, hc234zy, htr246c, htr267a, htr345a, htr456b, htr467a]
      ·
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc034zy, hc578zy, htr046a, htr345a, htr458a, htr467a, htr678a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr146a, htr147a, htr467c])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, hc234zy, hc578zy, htr246a, htr345a, htr458a, htr467a, htr678a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr245a, htr246b, htr267a, htr345a, htr567a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr267a, htr268a, htr678c])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr467a, htr468a, htr678c])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        rcases m.htr 1 4 5 (by decide) (by decide) with
          ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
        ·
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc146xy, hc234zy, htr013a, htr016a, htr134a, htr145a, htr245a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc147xy, hc234zy, htr013a, htr017a, htr134a, htr145a, htr245a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc148xy, hc234zy, htr013a, htr018a, htr134a, htr145a, htr245a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr145a, htr148a, htr458b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc012yx, hc578zy, htr016a, htr025a, htr167a, htr258a, htr678a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc146yz, htr046a, htr047a, htr167a, htr467b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc156yz, htr017b, htr078a, htr167b, htr567a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc156yz, htr167b, htr178a, htr567a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc146yz, htr167a, htr246a, htr247a, htr467b])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc146yz, hc346xy, htr167a, htr245a, htr246a, htr345a, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr013b, htr036a, htr134a, htr367a, htr567a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc356yz, htr036a, htr037a, htr367c, htr567a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc346yz, hc348xy, htr036a, htr038a, htr245a, htr246a, htr345a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr367a, htr567a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc014yx, hc346yz, htr013a, htr045a, htr136a, htr245a, htr246a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr045a, htr046b, htr067a, htr345a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc356yz, htr136a, htr137a, htr367c, htr567a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc346yz, hc348xy, htr136a, htr138a, htr245a, htr246a, htr345a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc026xy, hc568zy, htr025a, htr067a, htr167a, htr168a, htr258a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc146yz, htr046a, htr048a, htr168a, htr468b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc234zy, htr045a, htr048a, htr248a, htr345a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, htr136b, htr168a, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a]
          ·
            linarith only [hlam, hc012yx, hc578zy, htr013a, htr025a, htr137a, htr258a, htr378a]
        ·
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hd16b, hd34a, htr013a, htr016a, htr134c, htr145a, htr345a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd17b, hd34a, htr013a, htr017a, htr134c, htr145a, htr345a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hd18b, hd34a, htr013a, htr018a, htr134c, htr145a, htr345a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc346xy, htr013b, htr036a, htr134c, htr145a, htr345a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc347xy, htr013b, htr037a, htr134c, htr145a, htr345a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc348xy, htr013b, htr038a, htr134c, htr145a, htr345a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, htr014b, htr045a, htr145a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc034zy, htr047a, htr145a, htr147a, htr345a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr014b, htr046b, htr067a, htr145a, htr345a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr067b, htr078a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc346xy, htr134c, htr136a, htr145a, htr345a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc347xy, htr134c, htr137a, htr145a, htr345a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc348xy, htr134c, htr138a, htr145a, htr345a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          rcases m.htr 1 6 7 (by decide) (by decide) with
            ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd56b, htr145a, htr146b, htr167a, htr345a, htr567a]
          ·
            linarith only [hlam, hc012yx, hc578zy, htr016a, htr025a, htr167a, htr258a, htr678a]

theorem shard_177 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr578a : m.d 7 8 + lam ≤ m.d 5 7)
    (htr578b : m.d 7 8 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 5 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr478a : m.d 7 8 + lam ≤ m.d 4 7)
    (htr478b : m.d 7 8 < m.d 4 8)
    (htr478c : m.d 4 8 < m.d 4 7)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    : False :=
  proof_shard_177 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr568a htr568b htr568c htr578a htr578b htr578c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr457a htr457b htr457c htr347a htr347b htr347c htr357a htr357b htr357c htr478a htr478b htr478c htr023a htr023b htr023c

#print axioms shard_177
end Jsp404.NoSatNineDBMTerminal
