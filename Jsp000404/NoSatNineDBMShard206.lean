import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_206 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 2 8)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr028c : m.d 0 8 < m.d 2 8)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr267a : m.d 6 7 + lam ≤ m.d 2 6)
    (htr267b : m.d 6 7 < m.d 2 7)
    (htr267c : m.d 2 7 < m.d 2 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < (7/2 : ℝ)*lam := by
    linarith only [hd04braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < (7/2 : ℝ)*lam := by
    linarith only [hd14braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < (7/2 : ℝ)*lam := by
    linarith only [hd24braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < (7/2 : ℝ)*lam := by
    linarith only [hd38braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hd12a, hd23b, htr012a, htr013a, htr135a, htr235a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hc123xy, htr012a, htr013b, htr035a, htr135a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
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
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc267zy, htr278a, htr567a, htr568a, htr678c])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc367zy, htr378a, htr567a, htr568a, htr678c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr013a, htr137a, htr378a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr013b, htr037a, htr137a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr123c, htr137a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc678xy, htr456a, htr458a, htr567a, htr568c])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
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
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc345yz, htr035a, htr036a, htr356c, htr456a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc345yz, htr024c, htr046a, htr245a, htr356a, htr456b])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc345yz, htr024c, htr048a, htr245a, htr356a, htr458b, htr568b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc345yz, htr036b, htr067a, htr356b, htr456a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc345yz, htr046c, htr068a, htr356a, htr456c, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr013c, htr036a, htr136a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc345yz, htr124c, htr146a, htr245a, htr356a, htr456b])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc345yz, htr124c, htr148a, htr245a, htr356a, htr458b, htr568b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc345yz, htr146c, htr168a, htr356a, htr456c, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr013c, htr036a, htr123c, htr236a])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc345yz, htr245a, htr246a, htr356a, htr456b])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc345yz, htr245a, htr248a, htr356a, htr458b, htr568b])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc345yz, htr246c, htr268a, htr356a, htr456c, htr568a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr126a, htr167a, htr268a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc145yz, hc678xy, htr015a, htr016a, htr168a, htr456a, htr567a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc678xy, htr016a, htr017a, htr167b, htr168a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr016a, htr018a, htr168b])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc123xy, hc678xy, htr012a, htr013c, htr016a, htr035c, htr056a, htr168a, htr567a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc678xy, htr056a, htr057a, htr567b, htr568a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr056a, htr058a, htr568b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc045yz, htr057a, htr124c, htr147a, htr245a, htr457b])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hd12a, hd78b, htr012a, htr014a, htr147a, htr478a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc348xy, hc678xy, htr014a, htr016a, htr036c, htr038a, htr067a, htr134b, htr168a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr013c, htr038a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          rcases m.htr 1 5 6 (by decide) (by decide) with
            ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a]
          ·
            linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a]
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hc123xy, hd45b, hd67a, htr012a, htr014a, htr124c, htr135a, htr245a, htr356a, htr567a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr135b, htr356a, htr567a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr135a, htr356a, htr567a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr035a, htr036a, htr356c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd38b, hd67a, htr035a, htr038a, htr356a, htr567a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, htr035b, htr056a, htr356a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr035b, htr057a, htr356a, htr567c])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc678xy, htr035b, htr058a, htr356a, htr567a, htr568c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, htr036b, htr067a, htr356b, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr013c, htr035a, htr136a, htr356c])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr013c, htr038a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr013a, htr014a, htr146a, htr456b, htr567a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc134yx, htr013a, htr014c, htr046a, htr146a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc457yx, htr014a, htr015a, htr125c, htr147a, htr245c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc134yx, htr013a, htr014c, htr047a, htr147a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr047a, htr048a, htr478b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr147a, htr148a, htr478b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc123xy, htr012a, htr015a, htr135a, htr156a, htr356a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc123xy, htr012a, htr015a, htr135a, htr157a, htr356a, htr567c])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr015c, htr058a, htr158a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr136b, htr167a, htr356b, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr123c, htr135a, htr236a, htr356c])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc134yx, hd45b, hd67a, htr135a, htr146a, htr245a, htr246a, htr356a, htr567a])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          rcases m.htr 2 4 7 (by decide) (by decide) with
            ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
          ·
            linarith only [hlam, hc123xy, hc467zy, htr124a, htr135a, htr247a, htr356a, htr567a]
          ·
            linarith only [hlam, hc134yx, hd45b, hd67a, htr135a, htr147a, htr245a, htr247a, htr356a, htr567a]
      ·
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc234zy, htr034a, htr036a, htr245a, htr346c, htr456c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc234zy, htr035b, htr056a, htr245a, htr345b, htr458a, htr568b])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr056a, htr057a, htr567c])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr056a, htr058a, htr245a, htr458a, htr567a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr035c, htr038b, htr058c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr056b, htr067a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr013c, htr036a, htr136a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr138a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc234zy, htr135b, htr156a, htr245a, htr345b, htr458a, htr568b])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr156a, htr567a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567c])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015c, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr156b, htr167a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr234c, htr236a, htr245a, htr346c, htr456c])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr245a, htr246a, htr456c])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr245a, htr247a, htr457c])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr245a, htr248a, htr458c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, htr245b, htr256a, htr458a, htr568b])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr245b, htr258a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc234zy, hc678xy, htr245a, htr246b, htr268a, htr346a, htr456a, htr567a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr245a, htr346a, htr348a, htr456c, htr458b, htr567a, htr568b])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc234zy, htr245a, htr345b, htr356a, htr458a, htr568b])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr135a, htr356a, htr567a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc123xy, hd24b, hd67a, htr012a, htr015a, htr135a, htr145c, htr245a, htr356a, htr567a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, htr014a, htr015a, htr145c])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr045a, htr046a, htr456c])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045a, htr048a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc234zy, htr046b, htr068a, htr246c, htr268a, htr346a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hd13b, hd67a, htr013a, htr016c, htr068a, htr567a, htr568a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr145a, htr147a, htr457c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr145a, htr148a, htr458c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc234zy, htr015a, htr018a, htr125c, htr148b, htr245c, htr348a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr016c, htr068a, htr168a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc234zy, htr015a, htr017a, htr125c, htr147b, htr245c, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr245a, htr356a, htr358a, htr458a, htr567a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr245a, htr346c, htr368a, htr456c, htr567a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        rcases m.htr 4 6 8 (by decide) (by decide) with
          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
        ·
          linarith only [hlam, hc234zy, htr246c, htr268a, htr346a, htr468a]
        ·
          linarith only [hlam, hd24b, hd67a, htr245a, htr456c, htr468a, htr567a, htr568a]
    ·
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd12a, hd45b, htr126a, htr268a, htr456a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, htr456a, htr458a, htr568c])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr456b, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
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
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc345yz, htr035a, htr036a, htr356c, htr456a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc345yz, htr024c, htr046a, htr245a, htr356a, htr456b])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
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
            linarith only [hlam, hc345yz, htr036b, htr068a, htr356b, htr456a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr036c, htr038b, htr068c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr013c, htr036a, htr136a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr013c, htr037a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr013c, htr038a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc345yz, htr124c, htr146a, htr245a, htr356a, htr456b])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr013c, htr036a, htr123c, htr236a])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc345yz, htr245a, htr246a, htr356a, htr456b])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, hc457yx, htr345b, htr347a, htr356a, htr456a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc458yx, htr345b, htr348a, htr356a, htr456a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hc123xy, hc678yz, htr013c, htr036a, htr125a, htr257a, htr368a, htr578a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
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
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc123xy, hc345yz, htr012a, htr013c, htr014a, htr035c, htr056a, htr124c, htr245a, htr356a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                linarith only [hlam, htr014b, htr017c, htr047b])
              obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hc458yx, htr045b, htr048a, htr056a, htr456a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr018a, htr018b, htr018c, _, _⟩
                linarith only [hlam, htr014b, htr018c, htr048b])
              obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc123xy, hc678yz, htr012a, htr013c, htr014b, htr036a, htr045b, htr057a, htr368a, htr578a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr056a, htr057c, htr078a, htr456a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              rcases m.htr 1 4 7 (by decide) (by decide) with
                ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
              ·
                linarith only [hlam, hc123xy, hc467zy, htr012a, htr013c, htr014a, htr036a, htr147a, htr367a]
              ·
                linarith only [hlam, hc124xy, htr012a, htr014b, htr047a, htr147a]
            ·
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd13b, hd34a, htr013a, htr014a, htr147a, htr347a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc134yx, htr013a, htr014c, htr047a, htr147a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, hd13b, hd34a, htr013a, htr014a, htr148a, htr348a])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hc134yx, htr013a, htr014c, htr048a, htr148a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              rcases m.htr 3 5 7 (by decide) (by decide) with
                ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc345yz, htr046c, htr067c, htr078a, htr357a, htr456c, htr578a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc345yz, htr146c, htr167c, htr178a, htr357a, htr456c, htr578a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                  linarith only [hlam, hc123xy, hc678yz, htr012a, htr013c, htr017a, htr036a, htr178a, htr368a])
                obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc123xy, hc345yz, htr013a, htr017a, htr124a, htr157b, htr245a, htr357a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                  linarith only [hlam, htr015a, htr017a, htr157b])
                obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
                have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                  linarith only [hlam, hc135yx, hc678yz, htr013a, htr016a, htr157a, htr168a, htr578a])
                obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr157a, htr567c])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc345yz, htr056a, htr057a, htr357a, htr456a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, htr057a, htr058a, htr578b])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                rcases m.htr 1 5 6 (by decide) (by decide) with
                  ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
                ·
                  linarith only [hlam, hc345yz, htr016a, htr017a, htr137b, htr156c, htr357b, htr456a]
                ·
                  linarith only [hlam, htr156a, htr157a, htr567c]
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, htr035b, htr057a, htr357a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, htr135b, htr157a, htr357a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd45b, hd67a, htr356a, htr357c, htr378a, htr456a, htr678a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 2 5 6 (by decide) (by decide) with
                  ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
                ·
                  rcases m.htr 0 1 5 (by decide) (by decide) with
                    ⟨htr015a, htr015b, htr015c, _, _⟩ | ⟨htr015a, htr015b, htr015c, _, _⟩
                  ·
                    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr125c, htr256a, htr456a]
                  ·
                    linarith only [hlam, hc123xy, hc145yz, htr013a, htr015a, htr125a, htr256a, htr456a]
                ·
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, htr256a, htr258a, htr568c])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  rcases m.htr 4 7 8 (by decide) (by decide) with
                    ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                  ·
                    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                      linarith only [hlam, hc134yx, hc678yz, htr013a, htr016a, htr147a, htr168a, htr478a])
                    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
                    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yz, htr012a, htr013c, htr017a, htr036a, htr147c, htr368a, htr478a])
                    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, htr047c, htr078a, htr478a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc134yx, htr013a, htr017a, htr147a, htr178a, htr478a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yz, htr013c, htr036a, htr124a, htr247a, htr368a, htr478a])
                    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
                    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                      linarith only [hlam, hc134yx, hc145yz, htr013a, htr015a, htr147a, htr245a, htr247a])
                    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
                    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                      linarith only [hlam, hc134yx, hc345yz, htr013c, htr035c, htr056a, htr147a, htr245a, htr247a, htr356a])
                    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                    rcases m.htr 1 5 6 (by decide) (by decide) with
                      ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
                    ·
                      linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a]
                    ·
                      linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a]
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, hc457zy, htr035b, htr058a, htr357a, htr478a, htr578c])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                      linarith only [hlam, hc457zy, htr135b, htr158a, htr357a, htr478a, htr578c])
                    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                      linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr478a, htr678a])
                    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
                    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
                      linarith only [hlam, hc123xy, hc457zy, htr013a, htr015a, htr124a, htr135b, htr247a, htr357a])
                    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
                    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                      linarith only [hlam, hc123xy, hc467zy, htr013a, htr016a, htr124a, htr167a, htr247a])
                    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
                    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                      linarith only [hlam, hc025xy, hc457zy, htr024a, htr056a, htr247a, htr356a, htr357a])
                    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hd45b, hd67a, htr056a, htr057c, htr078a, htr456a, htr678a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
                      linarith only [hlam, hc123xy, hc467zy, htr012a, htr013c, htr017b, htr036a, htr078a, htr367a, htr478a])
                    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
                    rcases m.htr 1 5 6 (by decide) (by decide) with
                      ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
                    ·
                      linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a]
                    ·
                      linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a]
          ·
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr024c, htr047a, htr245a, htr457b, htr578a, htr678a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc467zy, htr047a, htr048a, htr458b, htr578b, htr678a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr124c, htr147a, htr245a, htr457b, htr578a, htr678a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr014a, htr014b, htr014c, _, _⟩
              linarith only [hlam, hc123xy, hc467zy, htr012a, htr013c, htr014a, htr036a, htr147a, htr367a])
            obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr014b, htr048a, htr148a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr457b, htr578a, htr678a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc123xy, hc467zy, htr013a, htr016a, htr124a, htr167a, htr247a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc025xy, hc467zy, htr024a, htr056a, htr247a, htr567c, htr578a, htr678a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr056a, htr057a, htr456a, htr578a, htr678a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr056a, htr058a, htr456a, htr578b, htr678a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc045yz, htr057b, htr078a, htr456a, htr567c, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc123xy, hc467zy, htr013a, htr017c, htr078a, htr124a, htr247a, htr678a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc145yz, hc167zy, htr015a, htr017a, htr456a, htr567c, htr578a, htr678a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, htr015b, htr018c, htr058b])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            rcases m.htr 1 5 6 (by decide) (by decide) with
              ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a]
            ·
              linarith only [hlam, hc125xy, htr012a, htr015b, htr057a, htr156a, htr567c]
        ·
          have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr014a, htr014b, htr014c, _, _⟩
            linarith only [hlam, hc123xy, hd45b, hd67a, htr012a, htr014a, htr124c, htr135a, htr245a, htr356a, htr567a])
          obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr135b, htr356a, htr567a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr135a, htr356a, htr567a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc123xy, hc168zy, htr012a, htr018a, htr135a, htr356a, htr568a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr035a, htr036a, htr356c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc367zy, htr035a, htr037a, htr356a, htr567a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc368zy, htr035a, htr038a, htr356a, htr568a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, htr035b, htr056a, htr356a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr035b, htr057a, htr356a, htr567c])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr035b, htr058a, htr356a, htr568c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, htr036b, htr067a, htr356b, htr568a, htr678b])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr036b, htr068a, htr356b, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr013c, htr035a, htr136a, htr356c])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr013c, htr037a, htr137a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr013c, htr038a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr013a, htr014a, htr146a, htr456b, htr567a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc134yx, htr013a, htr014c, htr046a, htr146a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc457yx, htr014a, htr015a, htr125c, htr147a, htr245c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc134yx, htr013a, htr014c, htr047a, htr147a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc458yx, htr014a, htr015a, htr125c, htr148a, htr245c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc134yx, hc467zy, htr047a, htr048a, htr135a, htr148a, htr356a, htr567a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc123xy, htr012a, htr015a, htr135a, htr156a, htr356a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc123xy, htr012a, htr015a, htr135a, htr157a, htr356a, htr567c])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc123xy, htr012a, htr015a, htr135a, htr158a, htr356a, htr568c])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr136b, htr167a, htr356b, htr568a, htr678b])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr136b, htr168a, htr356b, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr123c, htr135a, htr236a, htr356c])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hc134yx, hd45b, hd67a, htr135a, htr146a, htr245a, htr246a, htr356a, htr567a])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          rcases m.htr 2 4 7 (by decide) (by decide) with
            ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
          ·
            linarith only [hlam, hc123xy, hc467zy, htr124a, htr135a, htr247a, htr356a, htr567a]
          ·
            linarith only [hlam, hc134yx, hd45b, hd67a, htr135a, htr147a, htr245a, htr247a, htr356a, htr567a]
      ·
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc234zy, htr034a, htr036a, htr245a, htr346c, htr456c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc234zy, hc367zy, htr034a, htr037a, htr245a, htr456a, htr567a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc234zy, hc368zy, htr034a, htr038a, htr245a, htr456a, htr568a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc234zy, htr035b, htr056a, htr245a, htr345b, htr456a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr056a, htr057a, htr567c])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr056a, htr058a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr056b, htr067a, htr568a, htr678b])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr013c, htr036a, htr136a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr013c, htr037a, htr137a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr138a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc234zy, htr135b, htr156a, htr245a, htr345b, htr456a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr156a, htr567a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr156a, htr157a, htr567c])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr156a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr156b, htr167a, htr568a, htr678b])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, htr156b, htr168a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr236a, htr236b, htr236c, _, _⟩
          linarith only [hlam, htr234c, htr236a, htr245a, htr346c, htr456c])
        obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, htr245a, htr246a, htr456c])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr245a, htr247a, htr457c])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr245a, htr248a, htr458c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, htr245b, htr256a, htr456a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc234zy, htr245a, htr345b, htr356a, htr456a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr135a, htr356a, htr567a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123xy, hc168zy, htr012a, htr018a, htr135a, htr356a, htr568a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc123xy, hd24b, hd67a, htr012a, htr015a, htr135a, htr145c, htr245a, htr356a, htr567a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, htr014a, htr015a, htr145c])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr045a, htr046a, htr456c])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045a, htr048a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr145a, htr146a, htr456c])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc234zy, htr015a, htr016a, htr125c, htr146b, htr245c, htr346a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr145a, htr147a, htr457c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr145a, htr148a, htr458c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        rcases m.htr 2 7 8 (by decide) (by decide) with
          ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc678yz, htr127a, htr135a, htr278a, htr356a, htr568a]
        ·
          linarith only [hlam, hc137yx, hc267zy, htr135a, htr178a, htr278a, htr356a, htr567a]
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd13b, hd67a, htr013a, htr014a, htr134b, htr346a, htr456b, htr567a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr135b, htr345b, htr346a, htr456b, htr567a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc123xy, hc167zy, htr012a, htr017a, htr134a, htr346a, htr456b, htr567a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr035a, htr036a, htr345b, htr346c])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc367zy, htr035a, htr037a, htr345b, htr346a, htr456b, htr567a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hd38b, hd67a, htr035a, htr038a, htr345b, htr346a, htr456b, htr567a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hd04b, hd67a, htr045a, htr345a, htr346a, htr456b, htr567a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr034b, htr046a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, htr034b, htr047a, htr346a, htr467c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr036b, htr067a, htr346b, htr456b, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013c, htr034a, htr136a, htr346c])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr013c, htr038a, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    rcases m.htr 1 4 5 (by decide) (by decide) with
      ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
    ·
      linarith only [hlam, hc123xy, hc456yx, htr012a, htr014a, htr134a, htr145a, htr346a]
    ·
      linarith only [hlam, hd14b, hd67a, htr145a, htr345a, htr346a, htr456b, htr567a]

theorem shard_206 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 2 8)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr028c : m.d 0 8 < m.d 2 8)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr267a : m.d 6 7 + lam ≤ m.d 2 6)
    (htr267b : m.d 6 7 < m.d 2 7)
    (htr267c : m.d 2 7 < m.d 2 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    : False :=
  proof_shard_206 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr457a htr457b htr457c htr467a htr467b htr467c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr024a htr024b htr024c htr125a htr125b htr125c htr025a htr025b htr025c htr126a htr126b htr126c htr026a htr026b htr026c htr127a htr127b htr127c htr027a htr027b htr027c htr128a htr128b htr128c htr028a htr028b htr028c htr134a htr134b htr134c htr034a htr034b htr034c htr267a htr267b htr267c htr235a htr235b htr235c

#print axioms shard_206
end Jsp404.NoSatNineDBMTerminal
