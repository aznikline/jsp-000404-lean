import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_252 {lam p : ℝ} (m : NineModel lam p)
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
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  have hd04a := (m.hrange 0 4 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd18a, hd18braw⟩ := m.hrange 1 8 (by decide)
  have hd18b : m.d 1 8 < (7/2 : ℝ)*lam := by
    linarith only [hd18braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < (7/2 : ℝ)*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < (7/2 : ℝ)*lam := by
    linarith only [hd57braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc045zy, htr056a, htr345a, htr346a, htr456c])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hd01b, hd23a, htr012a, htr124c, htr146a, htr234a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr012a, htr015a, htr123a, htr156a])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr235a, htr236a, htr345c, htr346b])
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
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc456xy, htr235c, htr257a, htr345c, htr346a, htr457a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr235b, htr237c, htr257b])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc456xy, htr345c, htr346a, htr357a, htr457a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr056a, htr057a, htr235a, htr357a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr015b, htr057a, htr157a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc568yx, htr345a, htr346a, htr456c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc456xy, htr235c, htr258a, htr345c, htr346a, htr458a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr235b, htr238c, htr258b])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc456xy, htr345c, htr346a, htr358a, htr458a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr056a, htr058a, htr235a, htr358a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr015b, htr058a, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
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
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr012a, htr016a, htr123a, htr146c, htr456c, htr568a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr012a, htr017a, htr123a, htr157c, htr567c, htr568a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr012b, htr025a, htr123a, htr235c, htr345c, htr346a, htr456c, htr568a])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc023zy, hc678xy, htr036a, htr234a, htr346a, htr367a, htr456c, htr568a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc456xy, htr034a, htr036a, htr345a, htr346c])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc138xy, hd23a, hd68b, htr012a, htr013b, htr018a, htr034a, htr123a, htr346a, htr456c, htr568a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr034a, htr035a, htr235a, htr346a, htr456c, htr568a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr035a, htr037a, htr357b])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, htr035a, htr038a, htr358b])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, hd04a, hd68b, htr045a, htr345a, htr346a, htr456c, htr568a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr034c, htr046a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
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
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr056c, htr068a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr123a, htr125a, htr235c, htr345c, htr346a, htr456c, htr568a])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, hc013yx, hc268yz, htr012a, htr034a, htr128a, htr346a, htr456c, htr568a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hc023yx, hd23a, hd68b, htr028a, htr034a, htr123a, htr128a, htr346a, htr456c, htr568a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc238xy, hc678xy, htr026c, htr028a, htr067a, htr234a, htr346a, htr456c, htr568a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, htr012b, htr026a, htr126a])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr134a, htr134b, htr134c, _, _⟩
      linarith only [hlam, htr013b, htr034a, htr134a])
    obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
    have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr135a, htr135b, htr135c, _, _⟩
      linarith only [hlam, htr013b, htr035a, htr135a])
    obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, hd14a, hd68b, htr145a, htr345a, htr346a, htr456c, htr568a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr014b, htr047a, htr147a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    rcases m.htr 1 6 7 (by decide) (by decide) with
      ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
    ·
      linarith only [hlam, hd23a, hd68b, htr123a, htr126b, htr167a, htr456c, htr467a, htr568a]
    ·
      linarith only [hlam, hc013yx, hc678xy, htr016a, htr034a, htr167a, htr346a, htr456c, htr568a]
  ·
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd23a, hd56b, htr234a, htr346a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 1 3 4 (by decide) (by decide) with
      ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
    ·
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc456xy, htr134a, htr135a, htr345b, htr346a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr134a, htr136a, htr346b])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr135a, htr137a, htr357b])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr135a, htr138a, htr358b])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      rcases m.htr 2 4 5 (by decide) (by decide) with
        ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
      ·
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc234yz, htr012b, htr025a, htr124a, htr245c, htr345a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc023zy, htr034a, htr234b, htr245a, htr345a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc456xy, htr034a, htr035a, htr345b, htr346a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, htr034a, htr036a, htr346b])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr035a, htr037a, htr357b])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr035a, htr038a, htr358b])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr034c, htr046a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hc234yz, htr124a, htr125a, htr245c, htr345a])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
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
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc136xy, hd23a, hd78b, htr012a, htr016a, htr123a, htr135a, htr357a, htr578a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr012a, htr017a, htr123a, htr157c, htr578a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc138xy, hd23a, hd78b, htr012a, htr018a, htr123a, htr135a, htr357a, htr578a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr057c, htr078a, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hc013yx, hc278yz, htr012a, htr035a, htr128a, htr357a, htr578a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc023yx, hd23a, hd78b, htr028a, htr035a, htr123a, htr128a, htr357a, htr578a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc246yz, hc248xy, htr026a, htr028a, htr245a, htr345a, htr346a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc248xy, htr024c, htr028a, htr045a, htr245a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, htr045a, htr047a, htr457b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr012b, htr026a, htr126a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, htr014b, htr045a, htr145a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc013yx, hc678yz, htr016a, htr035a, htr168a, htr357a, htr578a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc236xy, htr026c, htr068a, htr123a, htr126b, htr168a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc013yx, htr017a, htr035a, htr178a, htr357a, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr012b, htr026a, htr123a, htr267a, htr567a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc236xy, htr012b, htr026b, htr067a, htr123a, htr267a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc156yz, htr067a, htr068a, htr167a, htr568a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 2 6 8 (by decide) (by decide) with
            ⟨htr268a, htr268b, htr268c, _, _⟩ | ⟨htr268a, htr268b, htr268c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd56b, htr012b, htr026a, htr123a, htr268a, htr568a]
          ·
            linarith only [hlam, hc236xy, htr123a, htr126b, htr168a, htr268a]
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
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc567zy, htr167a, htr168a, htr578a, htr678c])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc256yz, htr267a, htr567c, htr578a, htr678a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, hc013yx, hc567zy, htr012a, htr035a, htr126a, htr267a, htr357a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc236xy, htr012a, htr016a, htr123a, htr126c])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, htr016a, htr017a, htr167c])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, htr016a, htr018a, htr168c])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc246xy, htr124c, htr126a, htr145a, htr245a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457b])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr145a, htr148a, htr458b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc013yx, hc567zy, htr016a, htr035a, htr167c, htr178a, htr357a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, htr126c, htr168a, htr268a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc013yx, hc567zy, htr016a, htr035a, htr167a, htr357b, htr378a, htr578a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 3 4 7 (by decide) (by decide) with
            ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
          ·
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc014yx, hc467zy, htr016a, htr045a, htr167a, htr345a, htr347a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc246xy, htr024c, htr026a, htr045a, htr245a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, htr026a, htr027a, htr267c])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, htr026a, htr028a, htr268c])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr034c, htr047a, htr347a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd24a, hd57b, htr045a, htr047b, htr078a, htr245a, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hc246xy, hc247yz, htr126a, htr127a, htr245a, htr345a, htr347a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, hc567zy, htr127b, htr128a, htr178a, htr268b, htr578a, htr678b])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc024zy, htr048a, htr124a, htr128a, htr248c])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            rcases m.htr 2 7 8 (by decide) (by decide) with
              ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr278a, htr578a]
            ·
              linarith only [hlam, hc237xy, htr123a, htr127b, htr178a, htr278a]
          ·
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hc234yz, htr012b, htr027a, htr124a, htr247c, htr347a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hc234yz, htr124a, htr127a, htr247c, htr347a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc023yx, hc257yz, htr026a, htr035a, htr126a, htr127a, htr357a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc246xy, htr024c, htr026a, htr045a, htr245a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr045a, htr047a, htr457b])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, htr045a, htr048a, htr458b])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc236xy, htr026a, htr027c, htr078a, htr123b, htr135b, htr157b, htr178a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, htr127b, htr178a, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, hc234yz, htr012b, htr028a, htr124a, htr278c, htr347c, htr378a])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, hc236xy, htr026a, htr028a, htr123a, htr128a])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
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
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc456xy, htr012a, htr016a, htr124a, htr146c, htr245a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc456xy, htr012a, htr017a, htr124a, htr137c, htr245a, htr346c, htr367c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc456xy, htr012a, htr018a, htr124a, htr138c, htr245a, htr346c, htr368c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, htr012b, htr025a, htr124a, htr245c])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc456xy, htr012b, htr026a, htr124a, htr236c, htr245a, htr346c])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc456xy, htr012b, htr027a, htr124a, htr237c, htr245a, htr346c, htr367c])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc456xy, htr012b, htr028a, htr124a, htr238c, htr245a, htr346c, htr368c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc013yx, hc456xy, htr012a, htr034a, htr124a, htr245a, htr346a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr034a, htr035a, htr345c])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc456xy, htr034a, htr036a, htr345a, htr346c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr036a, htr037a, htr367c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr036a, htr038a, htr368c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, htr014b, htr045a, htr124b, htr245a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc023zy, htr034c, htr046a, htr234a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr036b, htr067a, htr368a, htr678b])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr036b, htr068a, htr368a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, htr124a, htr125a, htr245c])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr124a, htr126a, htr234a, htr236c, htr245a, htr346a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr124a, htr127a, htr234a, htr237c, htr245a, htr346a, htr367c])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr124a, htr128a, htr234a, htr238c, htr245a, htr346a, htr368c])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, htr124b, htr145a, htr245a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr124b, htr146b, htr167a, htr234a, htr245a, htr346a, htr368a, htr678b])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr124b, htr146b, htr168a, htr234a, htr245a, htr346a, htr368a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc023zy, hc567zy, htr036a, htr137c, htr178a, htr235a, htr357a, htr367c, htr678a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr234a, htr245a, htr246b, htr267a, htr346a, htr368a, htr678b])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc023zy, hc456xy, htr036a, htr234a, htr245a, htr246b, htr268a, htr346a, htr368a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr127b, htr178a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc013zy, htr036a, htr135b, htr157b, htr178a, htr367c, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc023zy, htr037c, htr078a, htr237a, htr378a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc457xy, hd01b, hd23a, htr012a, htr124a, htr237a, htr245a, htr378a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc023zy, hc678yz, htr034b, htr036a, htr047a, htr234a, htr368a, htr478a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc456xy, htr046a, htr047a, htr124b, htr147a, htr245a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc456xy, htr046a, htr047a, htr245a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, htr134c, htr147a, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          linarith only [hlam, hc023zy, hc678yz, htr036a, htr235a, htr357a, htr368a, htr578a]
        ·
          linarith only [hlam, hc023zy, hc567zy, htr036a, htr237a, htr367a, htr378a, htr578a]
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc456xy, htr012a, htr016a, htr123c, htr134a, htr146c, htr345a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd17b, hd23a, htr012a, htr017a, htr123c, htr134a, htr234a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hd18b, hd23a, htr012a, htr018a, htr123c, htr134a, htr234a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, htr012b, htr025a, htr123c, htr134a, htr235c, htr345c])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc236xy, htr012b, htr026a, htr123c, htr134a, htr234a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc237xy, htr012b, htr027a, htr123c, htr134a, htr234a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc238xy, htr012b, htr028a, htr123c, htr134a, htr234a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr013b, htr034a, htr134a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr013b, htr035a, htr134a, htr345c])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc456xy, htr013b, htr036a, htr134a, htr345a, htr346c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr036a, htr037a, htr367c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr036a, htr038a, htr368c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr014b, htr045a, htr134b, htr345a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc023zy, htr034c, htr046a, htr234a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr036b, htr067a, htr368a, htr678b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr036b, htr068a, htr368a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, htr123c, htr125a, htr134a, htr235c, htr345c])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc023zy, htr036a, htr123c, htr126a, htr134a, htr234a, htr236c])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc023zy, htr036a, htr123c, htr127a, htr134a, htr234a, htr237c, htr367c])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc023zy, htr036a, htr123c, htr128a, htr134a, htr234a, htr238c, htr368c])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, htr134a, htr135a, htr345c])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc023zy, htr036a, htr134a, htr136a, htr234a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr136a, htr137a, htr367c])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr136a, htr138a, htr368c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr134b, htr145a, htr345a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr136b, htr167a, htr368a, htr678b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr136b, htr168a, htr368a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr245a, htr245b, htr245c, _, _⟩
        linarith only [hlam, hd01b, hd24a, htr012a, htr123c, htr134a, htr245a, htr345a])
      obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd01b, hd45a, htr012a, htr123c, htr136a, htr245a, htr246b, htr267a, htr368a, htr678b])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd01b, hd45a, htr012a, htr123c, htr136a, htr245a, htr246b, htr268a, htr368a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd01b, hd67a, htr012a, htr123c, htr136a, htr367c, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc023zy, htr037c, htr078a, htr237a, htr378a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr017b, htr078a, htr178a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc123zy, hc457xy, htr134a, htr237a, htr345a, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc023zy, hc678yz, htr014b, htr036a, htr047a, htr134b, htr234a, htr368a, htr478a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc456xy, htr046a, htr047a, htr134b, htr147a, htr345a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc456xy, htr046a, htr047a, htr245a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr234c, htr247a, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        linarith only [hlam, hc023zy, hc678yz, htr036a, htr235a, htr357a, htr368a, htr578a]
      ·
        linarith only [hlam, hc023zy, hc567zy, htr036a, htr237a, htr367a, htr378a, htr578a]

theorem shard_252 {lam p : ℝ} (m : NineModel lam p)
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
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False :=
  proof_shard_252 m htr012a htr012b htr012c htr123a htr123b htr123c htr013a htr013b htr013c htr023a htr023b htr023c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr124a htr124b htr124c htr014a htr014b htr014c htr024a htr024b htr024c htr235a htr235b htr235c htr346a htr346b htr346c

#print axioms shard_252
end Jsp404.NoSatNineDBMTerminal
