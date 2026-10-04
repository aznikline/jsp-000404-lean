import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_052 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
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
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
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
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced124 := (m.htr 1 2 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr124a, htr124b, htr124c, _, _⟩
    linarith only [hlam, hc234xy, htr012a, htr013a, htr123b, htr124a])
  obtain ⟨htr124a, htr124b, htr124c, _, _⟩ := hforced124
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hc123yx, htr012b, htr013a, htr024a, htr124a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr125a, htr125b, htr125c, _, _⟩
    linarith only [hlam, hc235xy, htr012a, htr013a, htr123b, htr125a])
  obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hc123yx, htr012b, htr013a, htr025a, htr125a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc236xy, htr012a, htr013a, htr123b, htr126a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hc123yx, htr012b, htr013a, htr026a, htr126a])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc237xy, htr012a, htr013a, htr123b, htr127a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc123yx, htr012b, htr013a, htr027a, htr127a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc238xy, htr012a, htr013a, htr123b, htr128a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc123yx, htr012b, htr013a, htr028a, htr128a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hd12b, hd23a, htr012a, htr013a, htr134a, htr234a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hc123yx, htr012a, htr013c, htr034a, htr134a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr034a, htr035a, htr345b])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr034c, htr045a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, htr134a, htr135a, htr345b])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, htr134c, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr034a, htr036a, htr346b])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr034c, htr046a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013b, htr034a, htr136a, htr346b])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr134c, htr146a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, htr123b, htr134a, htr236a, htr346b])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr234c, htr246a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr234a, htr346b, htr367a, htr456a, htr567a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc067zy, htr078a, htr567a, htr568a, htr678c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc167zy, htr178a, htr567a, htr568a, htr678c])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr567a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr236b, htr238c, htr268b])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hd23a, hd45b, htr034a, htr038a, htr238a, htr345a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013b, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr246b, htr248c, htr268b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr027b, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc367zy, htr378a, htr567a, htr568a, htr678c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc678xy, htr456a, htr458a, htr567a, htr568c])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hd13a, hd45b, htr013a, htr014a, htr134c, htr345b, htr356a, htr456a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨htr015a, htr015b, htr015c, _, _⟩ | ⟨htr015a, htr015b, htr015c, _, _⟩
        ·
          linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr135c, htr356a, htr456a]
        ·
          linarith only [hlam, hc123yx, hc145yz, htr012a, htr015a, htr134a, htr345b, htr356a, htr456a]
      ·
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, htr356a, htr357a, htr567c])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc678xy, htr356a, htr358a, htr567a, htr568c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 0 1 4 (by decide) (by decide) with
          ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
        ·
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, htr014a, htr015a, htr145b])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr014a, htr016a, htr146b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc246yz, htr014a, htr018a, htr128b, htr134c, htr268b, htr346a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd13a, hd45b, htr013a, htr014b, htr046b, htr067a, htr456a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc123yx, hd45b, hd67a, htr012c, htr013a, htr014a, htr026c, htr068a, htr134c, htr345a, htr567a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc678xy, htr046b, htr048a, htr068a, htr458b, htr567a, htr568b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc347yx, htr013a, htr014a, htr134c, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc123yx, htr012a, htr013c, htr037a, htr137a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd13a, hd78b, htr013a, htr014a, htr147a, htr478a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc457yx, htr014a, htr017a, htr134c, htr147b, htr345a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc134xy, htr013a, htr014b, htr047a, htr147a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc457yx, hc678xy, htr046b, htr047a, htr056a, htr058a, htr068a, htr458a, htr567a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc457yx, htr047a, htr048a, htr134c, htr148a, htr345a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, htr015c, htr056a, htr156a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr015c, htr058a, htr158a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          rcases m.htr 1 6 8 (by decide) (by decide) with
            ⟨htr168a, htr168b, htr168c, _, _⟩ | ⟨htr168a, htr168b, htr168c, _, _⟩
          ·
            linarith only [hlam, hc123yx, hc678xy, htr012c, htr013a, htr014a, htr025c, htr056a, htr146b, htr168a, htr567a]
          ·
            linarith only [hlam, hc136xy, hc457yx, htr013a, htr014a, htr046b, htr047a, htr068a, htr134c, htr168a, htr345a]
        ·
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc123yx, hc457yx, htr012a, htr014a, htr134a, htr147a, htr345a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr034b, htr037c, htr047b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr047a, htr048a, htr478b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr013b, htr037a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr147a, htr148a, htr478b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, htr013b, htr037a, htr123b, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, htr124b, htr147a, htr247a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          rcases m.htr 3 4 7 (by decide) (by decide) with
            ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
          ·
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc123yx, hc178yz, htr012a, htr018a, htr134a, htr347a, htr478a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc123yx, hc467zy, htr012c, htr026c, htr068a, htr134a, htr347a, htr567a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc136xy, hc467zy, htr134a, htr168a, htr347a, htr567a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc123yx, hc467zy, htr125a, htr134a, htr256a, htr347a, htr567a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc245yz, htr026b, htr067a, htr256b, htr456a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc245yz, htr126b, htr167a, htr256b, htr456a, htr567a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc678xy, htr016a, htr018a, htr167a, htr168c])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc145yz, hc678xy, htr015a, htr016a, htr168a, htr456a, htr567a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc678xy, htr016a, htr017a, htr167b, htr168a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc123yx, hc678xy, htr012c, htr013a, htr016a, htr025c, htr056a, htr168a, htr567a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc678xy, htr056a, htr057a, htr567b, htr568a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr056a, htr058a, htr568b])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            rcases m.htr 1 5 6 (by decide) (by decide) with
              ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr156a, htr456a]
            ·
              linarith only [hlam, hc135xy, htr013a, htr015b, htr056a, htr156a]
          ·
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc124yx, hc145yz, htr012a, htr015a, htr147a, htr345a, htr347a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc124yx, hc146yz, htr012a, htr016a, htr147a, htr346a, htr347a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hd13a, hd45b, htr013a, htr017a, htr147c, htr345a, htr347a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc124yx, hc246yz, htr012a, htr018a, htr128b, htr147a, htr268b, htr346a, htr347a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc045yz, htr057a, htr345a, htr347a, htr457b])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc678xy, htr056a, htr057a, htr567b, htr568a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc678xy, htr056a, htr058a, htr567a, htr568c])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc124yx, hd45b, hd67a, htr012c, htr026c, htr068a, htr147a, htr345a, htr347a, htr567a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, htr015c, htr056a, htr156a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, htr015c, htr057a, htr157a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr015c, htr058a, htr158a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            rcases m.htr 1 6 8 (by decide) (by decide) with
              ⟨htr168a, htr168b, htr168c, _, _⟩ | ⟨htr168a, htr168b, htr168c, _, _⟩
            ·
              linarith only [hlam, hc678xy, htr016a, htr017a, htr157b, htr168a, htr567b]
            ·
              linarith only [hlam, hc136xy, htr013a, htr016b, htr068a, htr168a]
    ·
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd23a, hd45b, htr234a, htr346b, htr368a, htr456a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, htr456a, htr458a, htr568c])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr456b, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hd13a, hd45b, htr013a, htr014a, htr134c, htr345b, htr356a, htr456a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨htr015a, htr015b, htr015c, _, _⟩ | ⟨htr015a, htr015b, htr015c, _, _⟩
        ·
          linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr135c, htr356a, htr456a]
        ·
          linarith only [hlam, hc123yx, hc145yz, htr012a, htr015a, htr134a, htr345b, htr356a, htr456a]
      ·
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, htr356a, htr357a, htr567c])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr356a, htr358a, htr568c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          rcases m.htr 0 1 4 (by decide) (by decide) with
            ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
          ·
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, htr014a, htr015a, htr145b])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, htr014a, htr016a, htr146b])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hd13a, hd45b, htr013a, htr014b, htr046b, htr067a, htr456a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hd13a, hd45b, htr013a, htr014b, htr046b, htr068a, htr456a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hc347yx, htr013a, htr014a, htr134c, htr137a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hc123yx, htr012a, htr013c, htr037a, htr137a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, hc348yx, htr013a, htr014a, htr134c, htr138a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hc123yx, htr012a, htr013c, htr038a, htr138a])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hd13a, hd45b, htr013a, htr014a, htr145b, htr156a, htr456a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc135xy, htr013a, htr014b, htr045b, htr056a, htr156a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, htr056a, htr057a, htr567c])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr056a, htr058a, htr568c])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hc135xy, hc467zy, htr013a, htr014a, htr147a, htr156a, htr567a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc457yx, htr014a, htr017a, htr134c, htr147b, htr345a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc134xy, htr013a, htr014b, htr047a, htr147a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hc135xy, hc468zy, htr013a, htr014a, htr148a, htr156a, htr568a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc458yx, htr014a, htr018a, htr134c, htr148b, htr345a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc457yx, htr047a, htr048a, htr134c, htr148a, htr345a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc135xy, hc678yz, htr013a, htr017a, htr156a, htr178a, htr568a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc137xy, htr013a, htr017b, htr078a, htr178a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr237a, htr237b, htr237c, _, _⟩
              linarith only [hlam, htr013a, htr017a, htr123b, htr137c, htr237a])
            obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
            have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr238a, htr238b, htr238c, _, _⟩
              linarith only [hlam, htr013a, htr018a, htr123b, htr138c, htr238a])
            obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hc123yx, hc457yx, htr013a, htr014a, htr124a, htr134c, htr247a, htr345a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, hc458yx, htr134c, htr147a, htr247a, htr248a, htr345a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            rcases m.htr 2 5 6 (by decide) (by decide) with
              ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
            ·
              linarith only [hlam, hc135xy, hc245yz, htr013a, htr014a, htr134c, htr156a, htr256a, htr345a]
            ·
              linarith only [hlam, hc123yx, hd45b, hd67a, htr013a, htr014a, htr125a, htr134c, htr256a, htr345a, htr567a]
          ·
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hc123yx, hc457yx, htr012a, htr014a, htr134a, htr147a, htr345a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, htr034b, htr037c, htr047b])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, htr013b, htr037a, htr137a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hc123yx, hc458yx, htr012a, htr014a, htr134a, htr148a, htr345a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc124yx, htr012a, htr014c, htr048a, htr148a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr034b, htr038c, htr048b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, htr013b, htr038a, htr138a])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr237a, htr237b, htr237c, _, _⟩
              linarith only [hlam, htr013b, htr037a, htr123b, htr237a])
            obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
            have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr238a, htr238b, htr238c, _, _⟩
              linarith only [hlam, htr013b, htr038a, htr123b, htr238a])
            obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, htr124b, htr147a, htr247a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, htr124b, htr148a, htr248a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            rcases m.htr 3 4 7 (by decide) (by decide) with
              ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
            ·
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc123yx, hc467zy, htr125a, htr134a, htr256a, htr347a, htr567a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc245yz, htr026b, htr067a, htr256b, htr456a, htr567a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc245yz, htr026b, htr068a, htr256b, htr456a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc245yz, htr126b, htr167a, htr256b, htr456a, htr567a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hc123yx, hc467zy, htr012a, htr016a, htr134a, htr167a, htr347a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, htr016c, htr068a, htr168a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc123yx, hc467zy, htr127a, htr134a, htr278a, htr347a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr348a, htr348b, htr348c, _, _⟩
                linarith only [hlam, hc124yx, hc467zy, htr126a, htr148a, htr267a, htr347a, htr348a])
              obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc123yx, hc678yz, htr126a, htr134a, htr268a, htr347a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc045yz, htr057a, htr457c, htr478a, htr578a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc457zy, htr057a, htr058a, htr478a, htr578c])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc145yz, htr157a, htr457c, htr478a, htr578a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, hc123yx, hc457zy, htr012a, htr015a, htr134a, htr157a, htr347a])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr156a, htr456a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc135xy, htr013a, htr015b, htr056a, htr156a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, htr015c, htr058a, htr158a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              rcases m.htr 2 5 7 (by decide) (by decide) with
                ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
              ·
                linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a]
              ·
                linarith only [hlam, hc135xy, hc457zy, htr134a, htr156a, htr256a, htr257a, htr347a]
            ·
              have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                linarith only [hlam, hc124yx, hc145yz, htr012a, htr015a, htr147a, htr345a, htr347a])
              obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hc124yx, hc146yz, htr012a, htr016a, htr147a, htr346a, htr347a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, hd13a, hd45b, htr013a, htr017a, htr147c, htr345a, htr347a])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc045yz, htr057a, htr345a, htr347a, htr457b])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr016b, htr017c, htr057b, htr067a, htr567b])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd13a, hd45b, htr013a, htr016b, htr068a, htr456a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr047c, htr078a, htr345a, htr347a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr156a, htr456a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc135xy, htr013a, htr015b, htr056a, htr156a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, htr056a, htr058a, htr568c])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, htr015c, htr057a, htr157a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, htr156a, htr158a, htr568c])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc135xy, htr013a, htr016a, htr156a, htr168a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, htr017b, htr078a, htr178a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              rcases m.htr 2 5 6 (by decide) (by decide) with
                ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
              ·
                linarith only [hlam, hc145xy, hc245yz, htr147a, htr156a, htr256a, htr345a, htr347a]
              ·
                linarith only [hlam, hc124yx, hd45b, hd67a, htr125a, htr147a, htr256a, htr345a, htr347a, htr567a]
        ·
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr034a, htr037a, htr345a, htr357b, htr578a, htr678a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr034a, htr038a, htr345a, htr358b, htr578b, htr678a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr034c, htr047a, htr345a, htr457b, htr578a, htr678a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc467zy, htr047a, htr048a, htr458b, htr578b, htr678a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc056yz, htr067a, htr567c, htr578a, htr678a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr067a, htr068a, htr456a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr013b, htr037a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr013b, htr038a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr134c, htr147a, htr345a, htr457b, htr578a, htr678a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hc467zy, hd13a, hd45b, htr013a, htr014a, htr147a, htr456a, htr567c, htr578a, htr678a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr014b, htr048a, htr148a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc156yz, htr167a, htr567c, htr578a, htr678a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr167a, htr168a, htr456a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, htr013b, htr037a, htr123b, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, htr013b, htr038a, htr123b, htr238a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, htr024b, htr047a, htr247a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr024b, htr048a, htr248a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hd12b, hd67a, htr125a, htr256a, htr567c, htr578a, htr678a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr256a, htr257a, htr456a, htr578a, htr678a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc245yz, htr027b, htr078a, htr257b, htr456a, htr567c, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc245yz, htr127b, htr178a, htr257b, htr456a, htr567c, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hd12b, hd67a, htr012a, htr016a, htr167c, htr178a, htr678a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc145yz, hc167zy, htr015a, htr017a, htr456a, htr567c, htr578a, htr678a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc167zy, htr017a, htr018a, htr178b, htr678a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc123yx, hc167zy, htr012c, htr013a, htr017a, htr025c, htr056a, htr567c, htr578a, htr678a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr056a, htr057a, htr456a, htr578a, htr678a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr056a, htr058a, htr456a, htr578b, htr678a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          rcases m.htr 1 5 6 (by decide) (by decide) with
            ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr156a, htr456a]
          ·
            linarith only [hlam, hc135xy, htr013a, htr015b, htr056a, htr156a]
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc456yx, htr034a, htr036a, htr345a, htr346b])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc045yz, htr056a, htr345a, htr346a, htr456b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567c])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr056b, htr067a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc145yz, htr156a, htr345a, htr346a, htr456b])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr012a, htr015a, htr156a, htr567a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hc357yx, htr013a, htr015a, htr135c, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc123yx, htr012a, htr013c, htr037a, htr137a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hc358yx, htr013a, htr015a, htr135c, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc123yx, htr012a, htr013c, htr038a, htr138a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr156a, htr157a, htr567c])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr156b, htr167a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr123b, htr236a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, htr123b, htr137a, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, htr123b, htr138a, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc245yz, htr256a, htr345a, htr346a, htr456b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc123yx, hd45b, hd67a, htr013a, htr014a, htr125a, htr134c, htr256a, htr345a, htr567a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc123yx, hd45b, hd67a, htr013a, htr016a, htr125a, htr136c, htr256a, htr345a, htr346c, htr567a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, htr016a, htr017a, htr167c])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc024yx, hd45b, hd67a, htr025a, htr046a, htr256a, htr345a, htr346a, htr567a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, htr046a, htr047a, htr467c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    rcases m.htr 1 4 6 (by decide) (by decide) with
      ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
    ·
      linarith only [hlam, hc124yx, htr012a, htr014c, htr046a, htr146a]
    ·
      linarith only [hlam, hd12b, hd67a, htr012a, htr014a, htr146a, htr456b, htr567a]

theorem shard_052 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
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
    : False :=
  proof_shard_052 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c

#print axioms shard_052
end Jsp404.NoSatNineDBMTerminal
