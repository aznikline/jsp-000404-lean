import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_132 {lam p : ℝ} (m : NineModel lam p)
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
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr458a : m.d 4 5 + lam ≤ m.d 5 8)
    (htr458b : m.d 4 5 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr358a : m.d 3 5 + lam ≤ m.d 5 8)
    (htr358b : m.d 3 5 < m.d 3 8)
    (htr358c : m.d 3 8 < m.d 5 8)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd03a := (m.hrange 0 3 (by decide)).1
  obtain ⟨hd07a, hd07braw⟩ := m.hrange 0 7 (by decide)
  have hd07b : m.d 0 7 < (7/2 : ℝ)*lam := by
    linarith only [hd07braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hd45a, hd67b, htr123b, htr136a, htr234a, htr345a, htr356c, htr567a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hd45a, hd67b, htr234a, htr236a, htr345a, htr356c, htr567a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr126a, htr267a, htr456a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr356c, htr367a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, htr456c, htr467a, htr567a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc012yz, hd45a, hd78b, htr026a, htr123a, htr234a, htr267a, htr345a, htr678a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hd03a, hd78b, htr035a, htr356a, htr567a, htr678a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hd12b, hd35a, htr034a, htr035a, htr123a, htr234a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr034a, htr036a, htr123a, htr236a, htr345a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hd45a, hd78b, htr034a, htr037a, htr345a, htr357c, htr567c, htr678a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc358xy, hd45a, hd78b, htr034a, htr038a, htr345a, htr356a, htr567a, htr678a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd45a, hd78b, htr045a, htr046a, htr456c, htr567a, htr678a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hd07b, hd45a, htr078a, htr456a, htr567a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr013c, htr038a, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hd45a, hd78b, htr124b, htr146a, htr234b, htr345a, htr456c, htr567a, htr678a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc125yx, hd45a, hd78b, htr123a, htr156a, htr234a, htr345a, htr567a, htr678a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr012a, htr014a, htr145c, htr156a, htr456a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr156a, htr456a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc145zy, htr015a, htr016a, htr156b, htr456a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc127yx, hc145zy, htr015a, htr017a, htr123a, htr234a, htr345a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc128yx, hc145zy, htr015a, htr018a, htr123a, htr234a, htr345a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc145zy, htr016c, htr067a, htr156c, htr456a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr067a, htr068a, htr678b])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc457xy, htr145c, htr147a, htr156a, htr456a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, hc458xy, htr145c, htr148a, htr156a, htr456a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hd45a, hd78b, htr156a, htr157a, htr456a, htr567c, htr678a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc145zy, htr045a, htr047a, htr157a, htr457c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc145zy, htr156c, htr167a, htr456a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr023a, htr023b, htr023c, _, _⟩
      linarith only [hlam, hc012xy, hd45a, hd78b, htr016a, htr023a, htr167a, htr234a, htr345a, htr678a])
    obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hc278yz, hd12b, hd45a, htr023a, htr028a, htr123a, htr456a, htr567a, htr678a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
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
      linarith only [hlam, htr023c, htr037a, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, htr023c, htr038a, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr024a, htr026c, htr046b, htr246a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr024c, htr047a, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, hc458xy, htr024a, htr026a, htr236b, htr248a, htr345b, htr356b])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr045a, htr048a, htr123a, htr234c, htr248a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr023a, htr026a, htr123a, htr256b, htr456a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, htr025a, htr026a, htr256b])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr023a, htr025c, htr056a, htr123a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc578yz, htr056a, htr058a, htr567a, htr678a])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr256a, htr257a, htr567b])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc135zy, htr026a, htr027a, htr157a, htr236b, htr257c, htr356b])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, htr025b, htr058a, htr258a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc135zy, htr026a, htr028a, htr158a, htr236b, htr258c, htr356b])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr023a, htr026a, htr123a, htr246b, htr345a, htr346a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr023a, htr027a, htr123a, htr247b, htr345a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr248a, htr345a, htr348a]
    ·
      linarith only [hlam, hc478yz, hd12b, hd45a, htr123a, htr234a, htr348a, htr456a, htr567a, htr678a]
  ·
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045zy, htr056a, htr345a, htr346a, htr456c])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr056a, htr057a, htr567b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr056a, htr058a, htr458a, htr567a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr056c, htr067a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc012yz, hd45a, hd67b, htr025a, htr123a, htr125b, htr156a, htr234a, htr345a, htr567a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr025b, htr035c, htr235b])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hd12b, hd35a, htr034a, htr035a, htr123a, htr234a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr034a, htr036a, htr123a, htr236a, htr345a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr156a, htr157a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr156a, htr158a, htr458a, htr567a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr156c, htr167a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr246a, htr345a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc456xy, htr024a, htr025a, htr235b, htr246a, htr345b])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr023a, htr023b, htr023c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
      obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc012xy, hd45a, hd67b, htr015a, htr023a, htr156a, htr234a, htr345a, htr567a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc125yx, hd45a, hd67b, htr015a, htr016a, htr123a, htr156c, htr234a, htr345a, htr567a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr027a, htr127a, htr234a, htr345a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr028a, htr128a, htr234a, htr345a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc357xy, htr013a, htr015a, htr135b, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd13b, hd45a, htr034a, htr037a, htr137a, htr345a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc358xy, htr013a, htr015a, htr135b, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hd13b, hd45a, htr034a, htr038a, htr138a, htr345a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr012a, htr016a, htr146b, htr345a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, htr014a, htr016a, htr146b])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr012a, htr014c, htr046a, htr345a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr046a, htr047a, htr467b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr146a, htr147a, htr467b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc457xy, htr016a, htr017a, htr136b, htr147c, htr345a, htr346b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc678yx, hd12b, hd45a, htr012a, htr016a, htr168a, htr345a, htr346a, htr456c, htr567a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr056c, htr068a, htr136b, htr168a, htr345a, htr346b, htr567a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr046b, htr048c, htr068b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc458xy, htr016a, htr018a, htr136b, htr148c, htr345a, htr346b])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr012a, htr017a, htr137b, htr234a, htr237a, htr345a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr012a, htr018a, htr138b, htr234a, htr238a, htr345a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr024b, htr048a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr126b, htr168a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr034b, htr048a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr136b, htr168a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc678zy, hd12b, hd45a, htr012a, htr017a, htr178a, htr345a, htr346a, htr468a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc457xy, htr047c, htr078a, htr127b, htr178a, htr236b, htr267b, htr345a, htr346b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127b, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr137b, htr178a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        linarith only [hlam, hd45a, hd67b, htr345a, htr346a, htr467b, htr478a, htr678a]
      ·
        linarith only [hlam, hc457xy, htr127b, htr178a, htr236b, htr267b, htr345a, htr346b, htr478a]
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr045a, htr046a, htr123a, htr234a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc046zy, hd12b, hd45a, htr067a, htr123a, htr234a, htr346a, htr456a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr234b, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc146zy, hd12b, hd45a, htr123a, htr167a, htr234a, htr346a, htr456a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr234b, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr123a, htr234a, htr346a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr123a, htr236a, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr067a, htr068a, htr456a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr167a, htr168a, htr456a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr126b, htr168a, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        rcases m.htr 0 2 3 (by decide) (by decide) with
          ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hc124yx, htr012b, htr014a, htr023a, htr123a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc125yx, htr012b, htr015a, htr023a, htr123a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc126yx, htr012b, htr016a, htr023a, htr123a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, htr016a, htr017a, htr167b])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr016a, htr018a, htr168b])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr024a, htr024b, htr024c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
          obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc012yz, htr023b, htr034a, htr123a, htr234a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, htr034a, htr035a, htr345c])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr034a, htr036a, htr346c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc012yz, hc457xy, htr024a, htr123a, htr124b, htr147a, htr234a, htr345a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr134c, htr137b, htr147c])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd13b, hd45a, htr034a, htr037a, htr137a, htr345a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc012yz, hc458xy, htr024a, htr123a, htr124b, htr148a, htr234a, htr345a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr134c, htr138b, htr148c])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd13b, hd45a, htr034a, htr038a, htr138a, htr345a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, htr023c, htr037a, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, htr023c, htr038a, htr238a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc012yz, htr024a, htr124c, htr147a, htr247a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr045a, htr047a, htr123a, htr234c, htr247a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc012yz, htr024a, htr124c, htr148a, htr248a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr045a, htr048a, htr123a, htr234c, htr248a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr247a, htr345a, htr347a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc012yz, hc467yz, htr026a, htr123a, htr234a, htr267a, htr347a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc125yx, hc467yz, htr123a, htr156a, htr234a, htr347a, htr567a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc457yz, hd12b, hd45a, htr123a, htr156a, htr157a, htr234a, htr347a, htr456a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc467yz, hd12b, hd45a, htr123a, htr156a, htr158a, htr234a, htr347a, htr456a, htr568c, htr678c])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc127yx, hc467yz, htr123a, htr178a, htr234a, htr347a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr023a, htr026a, htr123a, htr256b, htr456a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, htr025a, htr026a, htr256b])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr023a, htr025c, htr056a, htr123a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr056a, htr057a, htr567b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr056a, htr058a, htr568b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, htr256a, htr257a, htr567b])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc135zy, htr026a, htr027a, htr157a, htr236b, htr257c, htr356b])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr256a, htr258a, htr568b])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc135zy, htr026a, htr028a, htr158a, htr236b, htr258c, htr356b])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr023a, htr027a, htr123a, htr278a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc135zy, htr057c, htr078a, htr157a, htr236b, htr267b, htr278a, htr356b])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr023a, htr028a, htr123a, htr248b, htr345a, htr348a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, htr237b, htr278a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, htr247b, htr278a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a]
          ·
            linarith only [hlam, hc135zy, htr157a, htr236b, htr267b, htr278a, htr356b, htr578a]
        ·
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
            linarith only [hlam, hd12b, hd45a, htr023a, htr027a, htr127a, htr234a, htr345a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hd12b, hd45a, htr023a, htr028a, htr128a, htr234a, htr345a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, htr023b, htr034a, htr234a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr023b, htr037a, htr234a, htr345a, htr357c, htr578a, htr678a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr023b, htr038a, htr234a, htr345a, htr358c, htr578c, htr678a])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr045a, htr047a, htr457c, htr578a, htr678a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc467yz, htr047a, htr048a, htr458c, htr578c, htr678a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc025yx, hd45a, hd67b, htr023a, htr056a, htr234a, htr345a, htr567b, htr578a, htr678a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr056a, htr057a, htr456a, htr578a, htr678a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr056a, htr058a, htr456a, htr578c, htr678a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc045zy, htr057c, htr078a, htr457a, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, htr013c, htr037a, htr137a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, htr013c, htr038a, htr138a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr124b, htr147a, htr234b, htr345a, htr457c, htr578a, htr678a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hc467yz, hd12b, hd45a, htr012a, htr014a, htr147a, htr457a, htr578a, htr678a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr014c, htr045c, htr058a, htr148a, htr458c])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc125yx, hd45a, hd67b, htr123a, htr156a, htr234a, htr345a, htr567b, htr578a, htr678a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr156a, htr456a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc145zy, htr015a, htr016a, htr156b, htr456a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, htr016a, htr018a, htr168b])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, htr015c, htr058a, htr157a, htr578b])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr015c, htr058a, htr158a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            rcases m.htr 1 7 8 (by decide) (by decide) with
              ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
            ·
              linarith only [hlam, hc012xy, hd45a, hd67b, htr016a, htr023a, htr167b, htr178a, htr234a, htr345a, htr678a]
            ·
              linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a]
          ·
            rcases m.htr 0 1 4 (by decide) (by decide) with
              ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
            ·
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hc012xy, hc457xy, htr014a, htr023a, htr147a, htr234a, htr345a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr137a, htr137b, htr137c, _, _⟩
                linarith only [hlam, htr134c, htr137b, htr147c])
              obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr023b, htr037a, htr137a, htr234a, htr345a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, hc012xy, hc458xy, htr014a, htr023a, htr148a, htr234a, htr345a])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr138a, htr138b, htr138c, _, _⟩
                linarith only [hlam, htr134c, htr138b, htr148c])
              obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr023b, htr038a, htr138a, htr234a, htr345a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr237a, htr237b, htr237c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr137a, htr234a, htr237a, htr345a])
              obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
              have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr238a, htr238b, htr238c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr138a, htr234a, htr238a, htr345a])
              obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
              rcases m.htr 3 4 7 (by decide) (by decide) with
                ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
              ·
                have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                  linarith only [hlam, hd12b, hd45a, htr012a, htr017a, htr147b, htr345a, htr347a])
                obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc045zy, htr057a, htr345a, htr347a, htr457c])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc145zy, htr157a, htr345a, htr347a, htr457c])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr147b, htr178a, htr345a, htr347a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                  linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr247a, htr345a, htr347a])
                obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
                have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                  linarith only [hlam, hc457xy, htr245c, htr247a, htr256a, htr456a])
                obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                  linarith only [hlam, htr256a, htr258a, htr568b])
                obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc457xy, htr037b, htr078a, htr345a, htr347b, htr478a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc457xy, htr237b, htr278a, htr345a, htr347b, htr478a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                  linarith only [hlam, hc012xy, hc678zy, htr016a, htr023a, htr168a, htr237a, htr378a])
                obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
                have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                  linarith only [hlam, hc126yx, hc145zy, htr015a, htr016a, htr123a, htr234a, htr345a])
                obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
                have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                  linarith only [hlam, hc126yx, hc178zy, htr016a, htr018a, htr123a, htr237a, htr378a])
                obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
                have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                  linarith only [hlam, hc146yx, htr014b, htr016a, htr047a, htr147a])
                obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc025yx, hc678zy, htr023a, htr056a, htr237a, htr378a, htr568a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc578zy, hd12b, hd45a, htr056a, htr058a, htr123a, htr237a, htr378a, htr456a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                rcases m.htr 1 5 6 (by decide) (by decide) with
                  ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
                ·
                  linarith only [hlam, hc125yx, htr012a, htr015c, htr056a, htr156a]
                ·
                  linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr156a, htr456a]
              ·
                have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                  linarith only [hlam, hc012xy, hc467yz, htr016a, htr023a, htr167a, htr234a, htr347a])
                obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
                have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                  linarith only [hlam, hc126yx, hc145zy, htr015a, htr016a, htr123a, htr234a, htr345a])
                obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
                have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                  linarith only [hlam, hc126yx, hc147zy, htr016a, htr017a, htr123a, htr234a, htr347a])
                obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
                have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                  linarith only [hlam, hc126yx, hc467yz, htr016a, htr018a, htr123a, htr168c, htr234a, htr347a, htr678c])
                obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc025yx, hc467yz, htr023a, htr056a, htr234a, htr347a, htr567a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc457yz, hd12b, hd45a, htr056a, htr057a, htr123a, htr234a, htr347a, htr456a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, htr057a, htr058a, htr578c])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr057b, htr078a, htr578a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                rcases m.htr 1 5 6 (by decide) (by decide) with
                  ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
                ·
                  linarith only [hlam, hc125yx, htr012a, htr015c, htr056a, htr156a]
                ·
                  linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr156a, htr456a]
            ·
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, htr014a, htr015a, htr145c])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, htr014a, htr016a, htr146c])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr137a, htr137b, htr137c, _, _⟩
                linarith only [hlam, hc347xy, htr013a, htr014a, htr124b, htr137a, htr234b])
              obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr023b, htr037a, htr137a, htr234a, htr345a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr138a, htr138b, htr138c, _, _⟩
                linarith only [hlam, hc348xy, htr013a, htr014a, htr124b, htr138a, htr234b])
              obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr023b, htr038a, htr138a, htr234a, htr345a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hd12b, hd45a, htr012a, htr014a, htr145c, htr156a, htr456a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc125yx, htr012a, htr014c, htr045c, htr056a, htr156a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, htr056a, htr057a, htr567b])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, htr056a, htr058a, htr568b])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hc125yx, hc467yz, htr012a, htr014a, htr147a, htr156a, htr567a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hc457xy, htr014a, htr017a, htr124b, htr147c, htr234b, htr345a])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, hc125yx, hc468yz, htr012a, htr014a, htr148a, htr156a, htr568a])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, hc458xy, htr014a, htr018a, htr124b, htr148c, htr234b, htr345a])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hc457xy, htr047a, htr048a, htr124b, htr148a, htr234b, htr345a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc125yx, hc678zy, htr012a, htr017a, htr156a, htr178a, htr568a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr237a, htr237b, htr237c, _, _⟩
                linarith only [hlam, hd12b, hd45a, htr012a, htr017a, htr137b, htr234a, htr237a, htr345a])
              obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
              have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr238a, htr238b, htr238c, _, _⟩
                linarith only [hlam, hd12b, hd45a, htr012a, htr018a, htr138b, htr234a, htr238a, htr345a])
              obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
              have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                linarith only [hlam, htr124b, htr147a, htr247a])
              obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
              have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr248a, htr248b, htr248c, _, _⟩
                linarith only [hlam, htr124b, htr148a, htr248a])
              obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, htr125b, htr156a, htr256a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, htr127b, htr178a, htr278a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr347a, htr347b, htr347c, _, _⟩
                linarith only [hlam, htr124b, htr147a, htr234b, htr347a])
              obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
              have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr348a, htr348b, htr348c, _, _⟩
                linarith only [hlam, htr124b, htr148a, htr234b, htr348a])
              obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, htr137b, htr178a, htr378a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hd45a, hd67b, htr124b, htr147a, htr234b, htr345a, htr478a, htr678a]
              ·
                linarith only [hlam, hc457xy, htr124b, htr147b, htr178a, htr234b, htr345a, htr478a]
      ·
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd03a, hd67b, htr035a, htr356b, htr368a, htr567a, htr568a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hd12b, hd35a, htr034a, htr035a, htr123a, htr234a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr034a, htr036a, htr345a, htr368a, htr567a, htr568a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc367xy, hd45a, hd67b, htr034a, htr037a, htr345a, htr368a, htr567a, htr568a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr034a, htr038a, htr345a, htr368c, htr567a, htr568a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr045a, htr048a, htr468c, htr567a, htr568a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc045zy, htr056a, htr456b, htr468a, htr568a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr056a, htr057a, htr567b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr056a, htr058a, htr458a, htr567a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc067yz, htr078a, htr567a, htr568a, htr678b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr013c, htr037a, htr137a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr138a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr124b, htr148a, htr234b, htr345a, htr468c, htr567a, htr568a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc145zy, htr156a, htr456b, htr468a, htr568a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc012yz, hd45a, hd67b, htr025a, htr123a, htr125b, htr156a, htr234a, htr345a, htr567a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567b])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr156a, htr158a, htr458a, htr567a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc126yx, hd45a, hd67b, htr123a, htr168a, htr234a, htr345a, htr567a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hd12b, hd46a, htr012a, htr014a, htr146c, htr168a, htr468a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr168a, htr468a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc125yx, hc146zy, htr015a, htr016a, htr123a, htr234a, htr346a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc678yx, htr015a, htr017a, htr156a, htr167b, htr168a, htr567a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr015a, htr018a, htr158b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr023a, htr023b, htr023c, _, _⟩
          linarith only [hlam, hc012xy, hd45a, hd67b, htr015a, htr023a, htr156a, htr234a, htr345a, htr567a])
        obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc267yz, hd12b, hd46a, htr023a, htr027a, htr123a, htr468a, htr567a, htr568a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc467xy, htr146c, htr147a, htr168a, htr468a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr023c, htr037a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr023c, htr038a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc457xy, htr024a, htr025a, htr235b, htr247a, htr345b])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hd12b, hd45a, htr045a, htr047a, htr123a, htr234c, htr247a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024c, htr048a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hd12b, hd46a, htr023a, htr025a, htr123a, htr256a, htr468a, htr568a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc125yx, htr023a, htr025a, htr123a, htr158a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr027c, htr078a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        rcases m.htr 3 4 7 (by decide) (by decide) with
          ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
        ·
          linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr247a, htr345a, htr347a]
        ·
          linarith only [hlam, hc467yz, hd12b, hd46a, htr123a, htr234a, htr347a, htr468a, htr567a, htr568a]

theorem shard_132 {lam p : ℝ} (m : NineModel lam p)
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
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr458a : m.d 4 5 + lam ≤ m.d 5 8)
    (htr458b : m.d 4 5 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr358a : m.d 3 5 + lam ≤ m.d 5 8)
    (htr358b : m.d 3 5 < m.d 3 8)
    (htr358c : m.d 3 8 < m.d 5 8)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    : False :=
  proof_shard_132 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr013a htr013b htr013c htr045a htr045b htr045c htr125a htr125b htr125c htr126a htr126b htr126c htr127a htr127b htr127c htr128a htr128b htr128c htr135a htr135b htr135c htr145a htr145b htr145c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr356a htr356b htr356c htr457a htr457b htr457c htr357a htr357b htr357c htr458a htr458b htr458c htr358a htr358b htr358c htr567a htr567b htr567c

#print axioms shard_132
end Jsp404.NoSatNineDBMTerminal
