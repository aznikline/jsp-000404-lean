import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_204 {lam p : ℝ} (m : NineModel lam p)
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
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < (7/2 : ℝ)*lam := by
    linarith only [hd02braw, hp]
  obtain ⟨hd05a, hd05braw⟩ := m.hrange 0 5 (by decide)
  have hd05b : m.d 0 5 < (7/2 : ℝ)*lam := by
    linarith only [hd05braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, htr013a, htr014a, htr123b, htr124c])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
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
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc234yx, htr123b, htr124a, htr135a, htr235a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc346xy, htr123a, htr124a, htr234b, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc234yx, htr013b, htr036a, htr123b, htr124a, htr236a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr016a, htr016b, htr016c, _, _⟩
    linarith only [hlam, htr013c, htr016b, htr036c])
  obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc234yx, htr123b, htr124a, htr136a, htr236a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hc347xy, htr123a, htr124a, htr234b, htr237a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc234yx, htr013b, htr037a, htr123b, htr124a, htr237a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr017a, htr017b, htr017c, _, _⟩
    linarith only [hlam, htr013c, htr017b, htr037c])
  obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, hc234yx, htr123b, htr124a, htr137a, htr237a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hc348xy, htr123a, htr124a, htr234b, htr238a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc234yx, htr013b, htr038a, htr123b, htr124a, htr238a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr018a, htr018b, htr018c, _, _⟩
    linarith only [hlam, htr013c, htr018b, htr038c])
  obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, hc234yx, htr123b, htr124a, htr138a, htr238a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd01b, hd34a, htr012a, htr124a, htr245a, htr345a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc234yx, htr123a, htr124c, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr013a, htr136a, htr367a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd01b, hd34a, htr012a, htr124a, htr246a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc234yx, htr123a, htr124c, htr146a, htr246a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr346b, htr347c, htr367b])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hd01b, hd34a, htr012a, htr124a, htr247a, htr347a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc234yx, htr123a, htr124c, htr147a, htr247a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc015yx, hc357yz, htr013a, htr056a, htr137a, htr456a, htr457a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc056zy, htr067a, htr456a, htr457a, htr567c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr145c, htr157a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr146c, htr167a, htr456c, htr457a, htr567c])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245c, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr246c, htr267a, htr456c, htr457a, htr567c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr345c, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678yx, htr456a, htr457a, htr567c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc567xy, htr146c, htr168a, htr456c, htr457a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr146b, htr148c, htr168b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124b, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc567xy, htr246c, htr268a, htr456c, htr457a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr124b, htr148a, htr234b, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr136b, htr168a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc567xy, htr456c, htr457a, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hd34a, hd67b, htr067a, htr068a, htr346a, htr468a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd34a, hd67b, htr345a, htr457a, htr578a, htr678a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 0 2 3 (by decide) (by decide) with
        ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
      ·
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr024c, htr045a, htr245a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr024c, htr046a, htr246a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr046a, htr048a, htr468b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr045c, htr057a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc014yx, hc567xy, htr013a, htr045a, htr135a, htr356a, htr457a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr356a, htr358a, htr568b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc014yx, hc678zy, htr013a, htr046a, htr137a, htr378a, htr468a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc234yx, hc357yz, htr012b, htr023c, htr025a, htr037c, htr078a, htr124a, htr245c, htr378a, htr457a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc567xy, htr025c, htr026a, htr056a, htr246c, htr456c, htr457a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc234yx, hc357yz, htr023a, htr027c, htr078a, htr245a, htr378a, htr457a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc357yz, htr045c, htr058a, htr378a, htr457a, htr578b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr025a, htr124a, htr125a])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr026a, htr124a, htr126a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, htr012b, htr027a, htr127a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr025c, htr056a, htr124b, htr145b, htr156a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015b, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 1 7 8 (by decide) (by decide) with
          ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
        ·
          linarith only [hlam, hc234yx, htr023c, htr037c, htr078a, htr124a, htr127b, htr178a]
        ·
          linarith only [hlam, hc014yx, hc357yz, htr017a, htr045a, htr178a, htr378a, htr457a]
      ·
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
          linarith only [hlam, htr023a, htr027a, htr237c])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr023a, htr028a, htr238c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        rcases m.htr 3 5 6 (by decide) (by decide) with
          ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
        ·
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr456a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc567xy, htr045a, htr046a, htr456b, htr457a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, htr045a, htr047a, htr457b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr046a, htr048a, htr468b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr045c, htr057a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hc257yz, hd02b, hd35a, htr023a, htr123a, htr127a, htr356a, htr456a, htr457a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hc024yx, hc268yz, htr023a, htr046a, htr123a, htr128a, htr468a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc247xy, htr124a, htr127b, htr178a, htr278a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr356a, htr358a, htr568b])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hc357yz, hd02b, hd35a, htr023a, htr237c, htr278a, htr356a, htr378a, htr456a, htr457a]
          ·
            linarith only [hlam, hc014yx, hc678zy, htr013a, htr046a, htr137a, htr378a, htr468a]
        ·
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc014yx, hc567xy, htr013a, htr045a, htr135a, htr356a, htr457a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, htr045a, htr046a, htr456c])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc567xy, htr045a, htr047a, htr456a, htr457c])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr047a, htr048a, htr478c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc034zy, htr045c, htr057a, htr345a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr047b, htr078a, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          rcases m.htr 1 2 5 (by decide) (by decide) with
            ⟨htr125a, htr125b, htr125c, _, _⟩ | ⟨htr125a, htr125b, htr125c, _, _⟩
          ·
            linarith only [hlam, hc024zy, htr045a, htr124a, htr125a, htr245c]
          ·
            linarith only [hlam, hd02b, hd56a, htr023a, htr123a, htr125a, htr235b, htr356a]
    ·
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd01b, hd56a, htr013a, htr136a, htr368a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr346b, htr348c, htr368b])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hd01b, hd34a, htr012a, htr124a, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc234yx, htr123a, htr124c, htr148a, htr248a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        rcases m.htr 0 2 3 (by decide) (by decide) with
          ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
        ·
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc234yx, htr023a, htr024c, htr045a, htr245a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc234yx, htr023a, htr024c, htr046a, htr246a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc234yx, htr023a, htr024c, htr047a, htr247a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc234yx, htr023a, htr024c, htr048a, htr248a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc014yx, hc367yz, htr013a, htr047a, htr137a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, htr457c, htr458b, htr478c])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          rcases m.htr 3 5 6 (by decide) (by decide) with
            ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc345yz, htr046c, htr067a, htr356a, htr456c, htr568a, htr678c])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc345yz, htr046c, htr068a, htr356a, htr456c, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr016b, htr067a, htr167a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr016b, htr068a, htr168a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc345yz, htr246c, htr267a, htr356a, htr456c, htr568a, htr678c])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hc345yz, htr246c, htr268a, htr356a, htr456c, htr568a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, htr356a, htr357a, htr567b])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, htr356a, htr358a, htr568b])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr568a, htr678c])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc014yx, hc678zy, htr013a, htr046a, htr137a, htr378a, htr468a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc014yx, hc367yz, htr017a, htr046a, htr178a, htr378a, htr467a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc345yz, htr156b, htr167b, htr178a, htr356a, htr457c, htr478a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr156a, htr158a, htr568b])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              linarith only [hlam, hc345yz, htr356a, htr457c, htr478a, htr567b, htr578a]
            ·
              linarith only [hlam, hc345yz, htr356b, htr367b, htr378a, htr457a, htr578a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr035b, htr056a, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, htr135b, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, htr235b, htr256a, htr356a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
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
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, htr246c, htr267a, htr467a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc014yx, hc567yz, htr013a, htr046a, htr135a, htr357a, htr467a])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr356a, htr357a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc345yz, htr037b, htr078a, htr357b, htr457a, htr578a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc345yz, htr137b, htr178a, htr357b, htr457a, htr578a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc345yz, htr237b, htr278a, htr357b, htr457a, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc014yx, hc678zy, htr013a, htr046a, htr137a, htr378a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr025a, htr025b, htr025c, _, _⟩
                linarith only [hlam, hc234yx, hc456zy, htr023a, htr025a, htr124b, htr146b, htr168a, htr235b, htr356a, htr468a])
              obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
              have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr027a, htr027b, htr027c, _, _⟩
                linarith only [hlam, hc234yx, hc267yz, htr023a, htr027a, htr124b, htr146b, htr168a, htr467a, htr468a])
              obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc234yx, hc456zy, htr023c, htr035c, htr057a, htr124b, htr146b, htr168a, htr356a, htr357a, htr468a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc456zy, htr035b, htr058a, htr356a, htr468a, htr568c])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              rcases m.htr 0 6 8 (by decide) (by decide) with
                ⟨htr068a, htr068b, htr068c, _, _⟩ | ⟨htr068a, htr068b, htr068c, _, _⟩
              ·
                linarith only [hlam, hc016yx, hc456zy, htr013a, htr068a, htr135a, htr356a, htr468a]
              ·
                linarith only [hlam, hc567xy, htr056c, htr057a, htr068a, htr568a]
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc456zy, htr035b, htr057a, htr356a, htr467a, htr567c])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc456zy, htr035b, htr058a, htr356a, htr467a, htr568c, htr678c])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc016yx, hc456zy, htr013a, htr067a, htr135a, htr356a, htr467a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, htr067a, htr068a, htr678c])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, htr067b, htr078a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc456zy, htr135b, htr157a, htr356a, htr467a, htr567c])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hc456zy, htr135b, htr158a, htr356a, htr467a, htr568c, htr678c])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc346yz, htr137b, htr178a, htr367b, htr467a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hc456zy, htr235b, htr257a, htr356a, htr467a, htr567c])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                linarith only [hlam, hc456zy, htr235b, htr258a, htr356a, htr467a, htr568c, htr678c])
              obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc346yz, htr237b, htr278a, htr367b, htr467a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                linarith only [hlam, hc456zy, htr356a, htr358a, htr467a, htr568c, htr678c])
              obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a]
              ·
                linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a]
        ·
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
            linarith only [hlam, htr023a, htr027a, htr237c])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr023a, htr028a, htr238c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          rcases m.htr 3 5 6 (by decide) (by decide) with
            ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
          ·
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr457a, htr567b])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc345yz, htr045a, htr046a, htr356a, htr456b])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc345yz, htr045a, htr047a, htr356a, htr457b, htr567b])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc345yz, htr046c, htr067a, htr356a, htr456c, htr568a, htr678c])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc345yz, htr046c, htr068a, htr356a, htr456c, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, htr046b, htr048c, htr068b])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr016b, htr067a, htr167a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr016b, htr068a, htr168a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, htr026b, htr067a, htr267a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr026b, htr068a, htr268a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, htr356a, htr357a, htr567b])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, htr356a, htr358a, htr568b])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr568a, htr678c])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hc024yx, hc267yz, htr023a, htr046a, htr123a, htr127a, htr467a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd24a, hd67b, htr027b, htr078a, htr124a, htr127a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc247xy, htr124a, htr127b, htr178a, htr278a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc024yx, hc367yz, htr023a, htr046a, htr237c, htr278a, htr378a, htr467a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc015yx, hc678zy, htr013a, htr056a, htr137a, htr378a, htr568a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc345yz, htr056a, htr057a, htr356a, htr457a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc578zy, htr057a, htr058a, htr357c, htr378a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, hc234yx, hc678zy, htr026b, htr068a, htr124a, htr126a, htr237a, htr378a])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hd02b, hd35a, htr023a, htr123a, htr126a, htr256b, htr356a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr125a, htr125b, htr125c, _, _⟩
              linarith only [hlam, htr125a, htr126a, htr256b])
            obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hd02b, hd35a, htr023a, htr123a, htr125c, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, htr156a, htr157a, htr567b])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr156a, htr158a, htr568b])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            rcases m.htr 2 5 7 (by decide) (by decide) with
              ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
            ·
              linarith only [hlam, hc345yz, htr126a, htr127a, htr236b, htr257c, htr356b, htr457a]
            ·
              linarith only [hlam, htr256a, htr257a, htr567b]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr035b, htr056a, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr125a, htr125b, htr125c, _, _⟩
              linarith only [hlam, hd02b, hd56a, htr023a, htr123a, htr125a, htr235b, htr356a])
            obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc024zy, htr045a, htr124a, htr125a, htr245c])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hd24a, hd45b, htr025b, htr057a, htr124a, htr125a, htr457a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc234yx, hc568xy, htr025b, htr058a, htr124a, htr125a, htr235a, htr356a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, htr135b, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc234yx, htr124a, htr125a, htr235a, htr256a, htr356a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hd24a, hd45b, htr124a, htr125a, htr257a, htr457a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hd02b, hd56a, htr023a, htr135b, htr157a, htr235c, htr257a, htr356a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, hd05b, hd24a, htr058a, htr124a, htr125a, htr258a])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, hd02b, hd56a, htr023a, htr135b, htr158a, htr235c, htr258a, htr356a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd02b, hd56a, htr023a, htr235c, htr257a, htr356a, htr357a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc017yx, hc567yz, htr013a, htr078a, htr135a, htr357a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, hd02b, hd56a, htr023a, htr235c, htr258a, htr356a, htr358a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr458a, htr458b, htr458c, _, _⟩
              linarith only [hlam, hc234yx, htr124a, htr125a, htr235a, htr245c, htr358a, htr458a])
            obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc567yz, hd01b, hd34a, htr013a, htr135a, htr347a, htr357a, htr478a, htr678a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd45b, hd57a, htr045a, htr047a, htr478a, htr578a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc457zy, hd01b, hd34a, htr013a, htr046a, htr047a, htr135a, htr346a, htr357a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc457zy, htr047a, htr048a, htr478b, htr578a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, hc234yx, hc567yz, htr026b, htr067a, htr124a, htr126a, htr235a, htr357a])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr016b, htr067a, htr167a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr016b, htr068a, htr168a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hd02b, hd57a, htr023a, htr123a, htr126a, htr267a, htr578a, htr678a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hc026yx, htr023a, htr068a, htr123a, htr126a, htr268a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd01b, hd57a, htr013a, htr137a, htr378a, htr578a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              linarith only [hlam, hc014yx, hc567yz, htr013a, htr046a, htr135a, htr357a, htr467a]
            ·
              linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a]
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc016yx, hc345yz, htr013a, htr068a, htr135a, htr456a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc067yz, htr078a, htr567a, htr568a, htr678b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hd01b, hd68a, htr016a, htr167a, htr567a, htr568a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc167yz, htr178a, htr567a, htr568a, htr678b])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc267yz, htr278a, htr567a, htr568a, htr678b])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr457a, htr567b])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc345yz, htr045a, htr046a, htr356a, htr456b])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc345yz, htr045a, htr047a, htr356a, htr457b, htr567b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc345yz, htr046c, htr067a, htr356a, htr456c, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc345yz, htr246c, htr267a, htr356a, htr456c, htr567a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc345yz, htr236b, htr268a, htr356b, htr456a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc458yx, htr345b, htr348a, htr356a, htr456a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hd01b, hd34a, htr012a, htr124a, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc234yx, htr123a, htr124c, htr148a, htr248a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, htr356a, htr357a, htr567b])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc678yx, htr356a, htr358a, htr567a, htr568b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc234yx, hc678yx, htr012b, htr026a, htr124a, htr236a, htr267a, htr368a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc235zy, hc678yx, htr025a, htr026a, htr268a, htr356a, htr567a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc678yx, htr026a, htr027a, htr267c, htr268a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr026a, htr028a, htr268c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc678yx, hd01b, hd34a, htr013a, htr046b, htr048a, htr067a, htr136a, htr348a, htr368a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc015yx, hc678yx, htr013a, htr056a, htr136a, htr368a, htr567a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc345yz, htr056a, htr057a, htr356a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr056a, htr058a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc234yx, hc678yx, htr124a, htr126a, htr236a, htr267a, htr368a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr023a, htr023b, htr023c, _, _⟩
          linarith only [hlam, hd02b, hd68a, htr023a, htr123a, htr126a, htr268a])
        obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr025a, htr124a, htr125a])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr027a, htr124a, htr127a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr126a, htr128a, htr268c])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc234yx, htr023a, htr025c, htr056a, htr124b, htr145b, htr156a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc345yz, htr156a, htr157a, htr356a, htr457a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr156a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 2 5 6 (by decide) (by decide) with
          ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
        ·
          linarith only [hlam, hc235yx, htr023a, htr025c, htr056a, htr256a]
        ·
          linarith only [hlam, hd23b, hd68a, htr023a, htr025a, htr256a, htr568a]
  ·
    have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr023a, htr023b, htr023c, _, _⟩
      linarith only [hlam, hd02b, hd46a, htr023a, htr123a, htr124a, htr234b, htr346a])
    obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hc456yx, htr012b, htr025a, htr124a, htr234b, htr245c, htr346a])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc246zy, htr012b, htr026a, htr124a, htr234b, htr346a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr024c, htr045a, htr245a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014b, htr046a, htr124b, htr234b, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456yx, htr045a, htr046c, htr067a, htr346b, htr367a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr025a, htr124a, htr125a])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr026a, htr124a, htr126a])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr124b, htr146a, htr234b, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr016b, htr067a, htr167a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr234b, htr246a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr026b, htr067a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr234b, htr245a, htr346a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc456yx, htr035b, htr057a, htr345b, htr346a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, htr025c, htr027b, htr057c])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr027a, htr124a, htr127a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc456yx, htr135b, htr157a, htr345b, htr346a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc456yx, htr235b, htr257a, htr345b, htr346a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc236yx, hc567yz, htr023a, htr025a, htr026b, htr067b, htr078a, htr257a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, htr025c, htr028b, htr057c, htr078c])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, htr057c, htr058b, htr078c])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr028a, htr124a, htr128a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr025c, htr058a, htr124b, htr145b, htr158a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc236yx, htr023a, htr025c, htr057c, htr078a, htr126b, htr167b, htr178a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc235yx, htr023a, htr025c, htr058a, htr258a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc237yx, htr023a, htr025c, htr057c, htr078a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd23b, hd46a, htr023a, htr025a, htr257a, htr345b, htr346a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd23b, hd46a, htr023a, htr025a, htr258a, htr345b, htr346a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd23b, hd37a, htr023a, htr027a, htr278a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr025a, htr245a, htr258a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc016yx, htr012a, htr067a, htr124a, htr234b, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr012a, htr124a, htr234b, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc456yx, htr045a, htr046c, htr068a, htr468a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr016b, htr068a, htr168a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr026b, htr068a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, htr036b, htr068a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd23b, hd47a, htr023a, htr027a, htr278a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc456yx, hd01b, hd78a, htr012a, htr045a, htr047a, htr124a, htr234b, htr346a, htr478a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr014b, htr047a, htr147a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr014b, htr047a, htr124b, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr014b, htr047a, htr124b, htr234b, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc016yx, htr012a, htr068a, htr124a, htr234b, htr346a, htr456b, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      linarith only [hlam, hd23b, hd57a, htr023a, htr027a, htr278a, htr578a]
    ·
      linarith only [hlam, hd23b, hd78a, htr023a, htr025a, htr257a, htr578a]

theorem shard_204 {lam p : ℝ} (m : NineModel lam p)
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
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    : False :=
  proof_shard_204 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c

#print axioms shard_204
end Jsp404.NoSatNineDBMTerminal
