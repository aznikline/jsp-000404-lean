import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_074 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd04a := (m.hrange 0 4 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < (7/2 : ℝ)*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr035a, htr036a, htr345c, htr346b])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr034c, htr046a, htr346a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr035c, htr056a, htr345c, htr346a, htr456c])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, htr013b, htr034a, htr136a, htr346b])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr134c, htr146a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr135c, htr156a, htr345c, htr346a, htr456c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr123b, htr134a, htr236a, htr346b])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr234c, htr246a, htr346a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr235c, htr256a, htr345c, htr346a, htr456c])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc567yx, htr345a, htr346a, htr456c, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc456xy, htr035c, htr057a, htr345c, htr346a, htr457a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr035b, htr037c, htr057b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, htr013b, htr037a, htr137a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc456xy, htr135c, htr157a, htr345c, htr346a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr013b, htr037a, htr123b, htr237a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr025b, htr057a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc456xy, htr345c, htr346a, htr357a, htr457a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc123yx, hc567zy, htr127a, htr135a, htr278a, htr357a, htr678a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr237b, htr238c, htr278b])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hd23a, hd46b, htr035a, htr038a, htr238a, htr345c, htr346a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr013b, htr038a, htr138a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr257b, htr258c, htr278b])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc568yx, htr345a, htr346a, htr456c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hc456xy, htr035c, htr058a, htr345c, htr346a, htr458a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc456xy, htr135c, htr158a, htr345c, htr346a, htr458a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc456xy, htr345c, htr346a, htr358a, htr458a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr234a, htr346a, htr467a, htr567a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr013a, htr014a, htr134c, htr346a, htr456c, htr568a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr013a, htr015a, htr135c, htr345c, htr346a, htr456c, htr568a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc123yx, hc168yz, htr012a, htr018a, htr134a, htr346a, htr456c, htr568a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hd04a, hd68b, htr045a, htr345a, htr346a, htr456c, htr568a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc678xy, htr034c, htr047a, htr346a, htr456c, htr467b, htr568a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc468yz, htr034c, htr048a, htr346a, htr456c, htr568a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456xy, htr045a, htr046b, htr067a, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc123yx, hc678xy, htr012a, htr016c, htr067a, htr134a, htr346a, htr456c, htr568a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr036c, htr068a, htr346c, htr456c, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 1 4 5 (by decide) (by decide) with
      ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
    ·
      linarith only [hlam, hd14a, hd68b, htr145a, htr345a, htr346a, htr456c, htr568a]
    ·
      linarith only [hlam, hc456xy, htr014a, htr016a, htr136c, htr145a, htr346c]
  ·
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd23a, hd56b, htr234a, htr346a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr245a, htr247a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr245a, htr248a, htr458b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd13a, hd78b, htr013a, htr015a, htr135c, htr357a, htr578a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123yx, hc178yz, htr012a, htr018a, htr135a, htr357a, htr578a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr057c, htr078a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc123yx, hd24a, hd78b, htr012a, htr015a, htr135a, htr145b, htr245a, htr357a, htr578a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, htr014a, htr015a, htr145b])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc124yx, hc146yz, htr012a, htr016a, htr145a, htr345a, htr346a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc124yx, htr012a, htr014c, htr045a, htr145a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045a, htr048a, htr458b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr145a, htr147a, htr457b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr145a, htr148a, htr458b])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hd13a, hd56b, htr013a, htr016a, htr167a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc136xy, htr013a, htr016b, htr067a, htr167a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd13a, hd56b, htr013a, htr016a, htr168a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc136xy, htr013a, htr016b, htr068a, htr168a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr157c, htr178a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc146xy, hc246yz, htr145a, htr167a, htr267a, htr345a, htr346a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        rcases m.htr 2 6 8 (by decide) (by decide) with
          ⟨htr268a, htr268b, htr268c, _, _⟩ | ⟨htr268a, htr268b, htr268c, _, _⟩
        ·
          linarith only [hlam, hc146xy, hc246yz, htr145a, htr168a, htr268a, htr345a, htr346a]
        ·
          linarith only [hlam, hc123yx, hc678yz, htr126a, htr135a, htr268a, htr357a, htr578a]
      ·
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc056yz, htr067a, htr567c, htr578a, htr678a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc567zy, htr067a, htr068a, htr578a, htr678c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc156yz, htr167a, htr567c, htr578a, htr678a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc123yx, hc567zy, htr012a, htr016a, htr135a, htr167a, htr357a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr016c, htr068a, htr168a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc256yz, htr267a, htr567c, htr578a, htr678a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc123yx, hc567zy, htr013a, htr015a, htr126a, htr157a, htr267a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc567zy, htr267a, htr268a, htr578a, htr678c])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc123yx, hc567zy, htr013b, htr037a, htr126a, htr267a, htr378a, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        rcases m.htr 0 1 4 (by decide) (by decide) with
          ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
        ·
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hd13a, hd46b, htr013a, htr014b, htr045a, htr345a, htr346a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          rcases m.htr 1 4 5 (by decide) (by decide) with
            ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
          ·
            linarith only [hlam, htr014c, htr045a, htr145a]
          ·
            linarith only [hlam, hc456xy, htr014a, htr015a, htr134c, htr145b, htr346a]
        ·
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hd12b, hd24a, htr012a, htr014a, htr145a, htr245a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc124yx, htr012a, htr014c, htr045a, htr145a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, htr045a, htr047a, htr457b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr045a, htr048a, htr458b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457b])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr145a, htr148a, htr458b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, hc124yx, hc467zy, htr126a, htr145a, htr267a, htr345a, htr347a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd13a, hd46b, htr013a, htr017a, htr147c, htr346a, htr347a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hd46b, hd67a, htr047c, htr078a, htr346a, htr347a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr017b, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hd13a, hd46b, htr013a, htr018a, htr178c, htr346a, htr347c, htr378a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc567zy, htr347c, htr348a, htr378a, htr458c, htr578c, htr678a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hc467yx, htr346a, htr347c, htr378a, htr478a]
          ·
            linarith only [hlam, hd46b, hd67a, htr346a, htr347a, htr478a, htr678a]
    ·
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
      ·
        linarith only [hlam, hc123yx, hc456xy, htr013a, htr014a, htr124a, htr134c, htr245a, htr346a]
      ·
        linarith only [hlam, hc123yx, hc456xy, htr012a, htr014a, htr124b, htr134a, htr245a, htr346a]

theorem shard_074 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False :=
  proof_shard_074 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr024a htr024b htr024c htr125a htr125b htr125c htr025a htr025b htr025c htr126a htr126b htr126c htr026a htr026b htr026c htr127a htr127b htr127c htr027a htr027b htr027c htr128a htr128b htr128c htr028a htr028b htr028c htr134a htr134b htr134c htr034a htr034b htr034c htr235a htr235b htr235c htr135a htr135b htr135c htr035a htr035b htr035c htr346a htr346b htr346c

#print axioms shard_074
end Jsp404.NoSatNineDBMTerminal
