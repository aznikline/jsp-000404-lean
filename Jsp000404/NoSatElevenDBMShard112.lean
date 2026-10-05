import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_112 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd25a := (m.hrange 2 5 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr024b, htr025c, htr045b])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc256xy, htr024a, htr025a, htr123a, htr126a, htr234c])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc257xy, htr024a, htr025a, htr123a, htr127a, htr234c])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc258xy, htr024a, htr025a, htr123a, htr128a, htr234c])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc356xy, htr024a, htr025a, htr234c, htr235b, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc012yz, htr023b, htr036a, htr123a, htr236a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hc357xy, htr024a, htr025a, htr234c, htr235b, htr237a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc012yz, htr023b, htr037a, htr123a, htr237a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr024c, htr045a, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc456xy, htr024a, htr025a, htr245b, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc457xy, htr024a, htr025a, htr245b, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc458xy, htr024a, htr025a, htr245b, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, hc459xy, htr024a, htr025a, htr245b, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr023a, htr025a, htr123a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd12b, hd57a, htr023a, htr025a, htr123a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr023a, htr025a, htr123a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr023a, htr025a, htr123a, htr245b, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr124a, htr246a, htr345a, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr124a, htr247a, htr345a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr124a, htr248a, htr345a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr124a, htr249a, htr345a, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, htr245b, htr256a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, htr245b, htr257a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd12b, hd67a, htr123a, htr234a, htr346a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd12b, hd68a, htr123a, htr234a, htr346a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd12b, hd69a, htr123a, htr234a, htr346a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hd12b, hd610a, htr123a, htr234a, htr346a, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd12b, hd78a, htr123a, htr234a, htr347a, htr478a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hd12b, hd79a, htr123a, htr234a, htr347a, htr479a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, hd12b, hd710a, htr123a, htr234a, htr347a, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
    linarith only [hlam, hd12b, hd89a, htr123a, htr234a, htr348a, htr489a])
  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
    linarith only [hlam, hd12b, hd810a, htr123a, htr234a, htr348a, htr4810a])
  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
    linarith only [hlam, hd12b, hd910a, htr123a, htr234a, htr349a, htr4910a])
  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
  rcases m.htr 0 2 6 (by decide) (by decide) with
    ⟨htr026a, htr026b, htr026c, _, _⟩ | ⟨htr026a, htr026b, htr026c, _, _⟩
  ·
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc125zy, htr025a, htr026a, htr156a, htr256c])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd25a, hd78b, htr025a, htr026a, htr256c, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc467yz, htr156c, htr168a, htr478a, htr567a, htr678b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd25a, hd89b, htr025a, htr026a, htr126b, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a]
      ·
        linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a]
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc456yz, htr156a, htr157a, htr467a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd25a, hd56b, htr025a, htr026a, htr267a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr023a, htr027a, htr123a, htr267b, htr467a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc256xy, htr025a, htr026b, htr067a, htr267a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr023c, htr037c, htr078a, htr123a, htr467a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr027b, htr028c, htr078b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc456yz, htr157c, htr178a, htr467a, htr567c, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd25a, hd89b, htr025a, htr027a, htr127b, htr178a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd25a, hd78b, htr025a, htr028a, htr289a, htr789a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr128a, htr289a, htr468a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hd12b, hd48a, htr023c, htr036c, htr068a, htr123a, htr489a, htr689a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc468yz, htr068a, htr069a, htr489a, htr689b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd46a, hd910b, htr067a, htr069a, htr467a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc478yz, htr489a, htr679c, htr6910a, htr789c, htr8910a]
      ·
        linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]
  ·
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hd12b, hd46a, htr023a, htr026c, htr067a, htr123a, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hd12b, hd46a, htr023a, htr026c, htr068a, htr123a, htr468a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
      linarith only [hlam, hd12b, hd46a, htr023a, htr026c, htr069a, htr123a, htr469a])
    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
    have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
      linarith only [hlam, hd12b, hd46a, htr023a, htr026c, htr0610a, htr123a, htr4610a])
    obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr026b, htr067a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr026b, htr068a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, htr026b, htr069a, htr269a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, htr026b, htr0610a, htr2610a])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    rcases m.htr 0 2 7 (by decide) (by decide) with
      ⟨htr027a, htr027b, htr027c, _, _⟩ | ⟨htr027a, htr027b, htr027c, _, _⟩
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc125zy, htr025a, htr027a, htr157a, htr257c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc256yz, htr026a, htr027a, htr267c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        rcases m.htr 1 5 6 (by decide) (by decide) with
          ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a]
        ·
          linarith only [hlam, hd25a, hd78b, htr156a, htr157a, htr256a, htr567c, htr678a]
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd25a, hd67b, htr025a, htr027a, htr278a, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc457yz, htr157a, htr158a, htr258c, htr278b, htr478a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc467yz, htr478a, htr567a, htr568a, htr678b])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc467yz, htr478a, htr568c, htr589a, htr678c, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hd25a, hd89b, htr156a, htr158a, htr256a, htr589a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd89b, htr015a, htr156a, htr568a, htr689a]
        ·
          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a]
    ·
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd12b, hd47a, htr023a, htr027c, htr078a, htr123a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, hd12b, hd47a, htr023a, htr027c, htr079a, htr123a, htr479a])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
        linarith only [hlam, hd12b, hd47a, htr023a, htr027c, htr0710a, htr123a, htr4710a])
      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr027b, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, htr027b, htr079a, htr279a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, htr027b, htr0710a, htr2710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      rcases m.htr 0 2 8 (by decide) (by decide) with
        ⟨htr028a, htr028b, htr028c, _, _⟩ | ⟨htr028a, htr028b, htr028c, _, _⟩
      ·
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc125zy, htr025a, htr028a, htr158a, htr258c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc126zy, htr026a, htr028a, htr168a, htr268c])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc256yz, htr026a, htr028a, htr268c, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc267yz, htr027a, htr028a, htr278c, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd25a, hd89b, htr156a, htr158a, htr256a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr159a, htr159b, htr159c, _, _⟩
            linarith only [hlam, hc458yz, htr158a, htr159a, htr489a, htr589b])
          obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd25a, hd910b, htr156a, htr159a, htr256a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc458yz, htr489a, htr589c, htr5910a, htr8910a]
          ·
            linarith only [hlam, hc458yz, htr489b, htr4910a, htr589a, htr8910a]
        ·
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr567a, htr568a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hd46a, hd89b, htr467a, htr567a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc468yz, htr168a, htr169a, htr489a, htr689b])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd46a, hd910b, htr167a, htr169a, htr467a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc468yz, htr489a, htr689c, htr6910a, htr8910a]
          ·
            linarith only [hlam, hc468yz, htr489b, htr4910a, htr689a, htr8910a]
      ·
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hd12b, hd48a, htr023a, htr028c, htr089a, htr123a, htr489a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, hd12b, hd48a, htr023a, htr028c, htr0810a, htr123a, htr4810a])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, htr028b, htr089a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, htr028b, htr0810a, htr2810a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        rcases m.htr 0 2 9 (by decide) (by decide) with
          ⟨htr029a, htr029b, htr029c, _, _⟩ | ⟨htr029a, htr029b, htr029c, _, _⟩
        ·
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc256yz, htr026a, htr029a, htr269c, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc257yz, htr027a, htr029a, htr279c, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc267yz, htr027a, htr029a, htr279c, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc278yz, htr028a, htr029a, htr289c, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hd01a, hd79b, htr015a, htr156a, htr567a, htr679a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hd25a, hd79b, htr156a, htr157a, htr256a, htr579a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc145zy, htr157a, htr457b, htr478a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd25a, hd89b, htr256a, htr567a, htr678a, htr789a]
            ·
              linarith only [hlam, hd25a, hd79b, htr257a, htr578a, htr678a, htr679a]
          ·
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hd25a, hd69b, htr156a, htr157a, htr257a, htr569a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd46a, hd79b, htr467a, htr578a, htr579a, htr678a]
            ·
              linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a]
        ·
          rcases m.htr 0 2 10 (by decide) (by decide) with
            ⟨htr0210a, htr0210b, htr0210c, _, _⟩ | ⟨htr0210a, htr0210b, htr0210c, _, _⟩
          ·
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc256yz, htr0210a, htr026a, htr2610c, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, hc257yz, htr0210a, htr027a, htr2710c, htr5710a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc267yz, htr0210a, htr027a, htr2710c, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc278yz, htr0210a, htr028a, htr2810c, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hd01a, hd710b, htr015a, htr156a, htr567a, htr6710a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd25a, hd710b, htr156a, htr157a, htr256a, htr5710a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc145zy, htr157a, htr457b, htr478a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd25a, hd810b, htr256a, htr567a, htr678a, htr7810a]
              ·
                linarith only [hlam, hd25a, hd710b, htr257a, htr578a, htr6710a, htr678a]
            ·
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd25a, hd610b, htr156a, htr157a, htr257a, htr5610a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd01a, hd810b, htr015a, htr157a, htr578a, htr7810a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd46a, hd710b, htr467a, htr5710a, htr578a, htr678a]
              ·
                linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a]
          ·
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hd25a, hd78b, htr156a, htr157a, htr256a, htr567c, htr678a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc145zy, htr157a, htr457b, htr479a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hd25a, hd78b, htr257a, htr579a, htr678a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd25a, hd89b, htr256a, htr567a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hd25a, hd910b, htr256a, htr567a, htr679a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc478yz, htr489a, htr789c, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc146zy, htr167a, htr467b, htr478a, htr678a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc467yz, htr167a, htr168a, htr478a, htr678b])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc467yz, htr478a, htr567a, htr568a, htr678b])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc467yz, htr168c, htr189a, htr478a, htr678c, htr789a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, htr168b, htr169c, htr189b])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hd01a, hd89b, htr015a, htr156a, htr568a, htr689a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hd01a, hd910b, htr016a, htr168a, htr689a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd01a, hd89b, htr016a, htr169a, htr6910a, htr8910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hd25a, hd79b, htr156a, htr157a, htr256a, htr567c, htr679a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  rcases m.htr 5 7 8 (by decide) (by decide) with
                    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                  ·
                    linarith only [hlam, hd25a, hd79b, htr257a, htr578a, htr678a, htr679a]
                  ·
                    linarith only [hlam, hc145zy, htr157a, htr457b, htr478a, htr578a]
                ·
                  rcases m.htr 7 9 10 (by decide) (by decide) with
                    ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  ·
                    linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a]
                  ·
                    linarith only [hlam, hc467yz, htr479b, htr4910a, htr679a, htr7910a]
            ·
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc456yz, htr156a, htr157a, htr467a, htr567b])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd01a, hd910b, htr015a, htr157a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc478yz, htr489a, htr789c, htr7910a, htr8910a]
              ·
                linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]

theorem shard_112 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    : False :=
  proof_shard_112 m htr015a htr016a htr023a htr023b htr023c htr024a htr024b htr024c htr025a htr025c htr123a htr124a htr234a htr234c htr235b

#print axioms shard_112
end Jsp404.NoSatElevenDBMTerminal
