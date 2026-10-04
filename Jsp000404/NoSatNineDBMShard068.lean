import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_068 {lam p : ℝ} (m : NineModel lam p)
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
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr568a, htr678b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hc456yz, htr056a, htr058a, htr467a, htr568b, htr678b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, hc456yz, htr057c, htr078a, htr467a, htr567c, htr678a])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hd01a, hd56b, htr013a, htr134b, htr146a, htr467a, htr567a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, htr124c, htr126b, htr146c])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc456yz, htr146a, htr147a, htr467c, htr567a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, htr124c, htr127b, htr147c])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr568a, htr678b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc456yz, htr156a, htr157a, htr467a, htr567b])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc456yz, htr156a, htr158a, htr467a, htr568b, htr678b])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc456yz, htr157c, htr178a, htr467a, htr567c, htr678a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hc378yz, hc456yz, htr235a, htr238a, htr356a, htr467a, htr678a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr467a, htr567a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc238xy, hc456yz, htr124a, htr128a, htr235a, htr246a, htr356a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc456yz, htr246a, htr247a, htr467c, htr567a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr125b, htr157a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr235b, htr237c, htr257b])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr125b, htr158a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr127b, htr178a, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, htr134c, htr147a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc456yz, htr356a, htr357a, htr467a, htr567b])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc456yz, htr356a, htr358a, htr467a, htr568b, htr678b])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, htr456b, htr458a, htr467a, htr568b, htr678b])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, htr467a, htr468a, htr678b])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hc456yz, htr146a, htr148a, htr468c, htr568a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc456yz, htr246a, htr248a, htr468c, htr568a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, htr134c, htr148a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, htr467c, htr478a, htr678a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr018a, htr018b, htr018c, _, _⟩
    linarith only [hlam, hc123zy, hc178yz, htr013a, htr018a, htr235a, htr357a, htr578a])
  obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hd23a, hd78b, htr023a, htr025a, htr125b, htr157a, htr578a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr025b, htr045c, htr245b])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hd45a, hd56b, htr045a, htr046a, htr467a, htr567a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr045a, htr047a, htr124a, htr247a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr045a, htr048a, htr124a, htr248a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hd01a, hd78b, htr013a, htr135a, htr357a, htr578a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, hc123zy, htr013a, htr015a, htr135b, htr235a])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr016a, htr016b, htr016c, _, _⟩
    linarith only [hlam, htr015a, htr016a, htr156b])
  obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
  have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr017a, htr017b, htr017c, _, _⟩
    linarith only [hlam, htr015a, htr017a, htr157b])
  obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hc012xy, hc478yz, htr015a, htr024a, htr157a, htr248a, htr578a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc125yx, hc278yz, htr024a, htr028a, htr124a, htr157a, htr578a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hc234xy, htr023c, htr024a, htr035a, htr235a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr035a, htr036a, htr356b])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr035a, htr037a, htr357b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, hd23a, hd78b, htr135a, htr137a, htr235a, htr378a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc123zy, htr023a, htr027a, htr137a, htr237c])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc234xy, hc346zy, htr024a, htr027a, htr135a, htr136a, htr235a, htr247b, htr467b])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hc123zy, htr023a, htr026a, htr136a, htr236c])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hd34b, hd46a, htr036c, htr067a, htr134a, htr136a, htr467a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr067a, htr068a, htr678b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  rcases m.htr 1 3 8 (by decide) (by decide) with
    ⟨htr138a, htr138b, htr138c, _, _⟩ | ⟨htr138a, htr138b, htr138c, _, _⟩
  ·
    linarith only [hlam, hc234xy, hc456yz, htr024a, htr027a, htr135a, htr138a, htr235a, htr247b, htr358c, htr467b, htr568c]
  ·
    linarith only [hlam, hc123zy, htr023a, htr028a, htr138a, htr238c]

theorem shard_068 {lam p : ℝ} (m : NineModel lam p)
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
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    : False :=
  proof_shard_068 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr346a htr346b htr346c htr457a htr457b htr457c htr568a htr568b htr568c htr023a htr023b htr023c htr134a htr134b htr134c htr014a htr014b htr014c htr034a htr034b htr034c htr245a htr245b htr245c htr125a htr125b htr125c htr145a htr145b htr145c htr356a htr356b htr356c htr236a htr236b htr236c htr256a htr256b htr256c htr467a htr467b htr467c

#print axioms shard_068
end Jsp404.NoSatNineDBMTerminal
