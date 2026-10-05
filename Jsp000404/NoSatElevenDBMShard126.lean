import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_126 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  have hd37a := (m.hrange 3 7 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  have hd49a := (m.hrange 4 9 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr023c, htr025b, htr035c])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr024c, htr025b, htr045c])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, hc237xy, htr023a, htr025a, htr125a, htr127a])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr023a, htr025a, htr125a, htr234a])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr235a, htr235b, htr235c, _, _⟩
    linarith only [hlam, htr023b, htr035a, htr235a])
  obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc123zy, htr023a, htr025a, htr135a, htr235c])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hd12b, hd36a, htr023a, htr025a, htr125a, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hd12b, hd37a, htr023a, htr025a, htr125a, htr237a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr024b, htr045a, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hd12b, hd46a, htr024a, htr025a, htr125a, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hd12b, hd47a, htr024a, htr025a, htr125a, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hd12b, hd48a, htr024a, htr025a, htr125a, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, hd12b, hd49a, htr024a, htr025a, htr125a, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc234yz, htr024a, htr025a, htr245c, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 1 3 4 (by decide) (by decide) with
    ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
  ·
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr134a, htr136a, htr236a, htr345a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr134a, htr137a, htr237a, htr345a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hd01a, hd56b, htr013a, htr134a, htr345a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr023a, htr025a, htr256a, htr456a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hd01a, hd57b, htr013a, htr134a, htr345a, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr023a, htr025a, htr257a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd01a, hd58b, htr013a, htr134a, htr345a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr023a, htr025a, htr258a, htr458a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hd01a, hd59b, htr013a, htr134a, htr345a, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hd23a, hd45b, htr023a, htr025a, htr259a, htr459a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr013a, htr134a, htr346a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd01a, hd68b, htr013a, htr134a, htr346a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hd01a, hd69b, htr013a, htr134a, htr346a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd01a, hd78b, htr013a, htr134a, htr347a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr125a, htr258a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc456zy, htr346a, htr348a, htr468b, htr568a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr013a, htr134a, htr348a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a]
          ·
            linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a]
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hd12b, hd68a, htr025a, htr026a, htr125a, htr256b, htr568a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          rcases m.htr 2 6 7 (by decide) (by decide) with
            ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd46b, htr023a, htr026a, htr267a, htr467a]
          ·
            linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr567a, htr568a]
      ·
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr025a, htr026a, htr125a, htr256b, htr567a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hd23a, hd46b, htr023a, htr026a, htr268a, htr468a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hd23a, hd46b, htr023a, htr026a, htr269a, htr469a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr269a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr125a, htr256a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr125a, htr256a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr125a, htr256a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 3 4 7 (by decide) (by decide) with
          ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd01a, hd78b, htr013a, htr134a, htr347a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc467zy, htr347a, htr348a, htr478b, htr678a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr013a, htr134a, htr348a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a]
          ·
            linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc234yz, htr247a, htr347c, htr378a, htr478a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc234yz, htr247a, htr347c, htr379a, htr479a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd01a, hd910b, htr013a, htr137a, htr379a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
    ·
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc234yz, htr024a, htr026a, htr246c, htr346a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr025a, htr026a, htr125a, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr025a, htr026a, htr125a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hd12b, hd69a, htr025a, htr026a, htr125a, htr269a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc234yz, htr246a, htr346c, htr367a, htr467a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc234yz, htr246b, htr268a, htr346a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc234yz, htr246a, htr346c, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc234yz, htr246b, htr269a, htr346a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc234yz, htr246a, htr346c, htr369a, htr469a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd01a, hd79b, htr013a, htr136a, htr367a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd01a, hd910b, htr013a, htr136a, htr369a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr125a, htr258a, htr589a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr125a, htr259a, htr5910a, htr8910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hc267yz, htr279a, htr679c, htr6910a, htr7910a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hd12b, hd79a, htr025a, htr027a, htr125a, htr279a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr023a, htr027a, htr278a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 5 7 9 (by decide) (by decide) with
            ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
          ·
            linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
          ·
            linarith only [hlam, hd12b, hd79a, htr127a, htr278a, htr578a, htr579a]
        ·
          rcases m.htr 5 7 9 (by decide) (by decide) with
            ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
          ·
            linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]
          ·
            linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr579a, htr7910a, htr8910a]
      ·
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr025a, htr027a, htr125a, htr257b, htr578a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr023a, htr027a, htr279a, htr679a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr127a, htr279a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr125a, htr257a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr234b, htr246a, htr346a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr234b, htr247a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr234b, htr248a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr349a, htr349b, htr349c, _, _⟩
      linarith only [hlam, hc123zy, htr134a, htr234b, htr249a, htr349a])
    obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd23a, hd56b, htr134a, htr135a, htr234a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd23a, hd35b, htr023a, htr025a, htr256a, htr356a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd23a, hd57b, htr134a, htr135a, htr234a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd23a, hd35b, htr023a, htr025a, htr257a, htr357a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd23a, hd58b, htr134a, htr135a, htr234a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hd23a, hd35b, htr023a, htr025a, htr258a, htr358a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hd23a, hd59b, htr134a, htr135a, htr234a, htr359a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hd23a, hd35b, htr023a, htr025a, htr259a, htr359a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    rcases m.htr 1 3 6 (by decide) (by decide) with
      ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
    ·
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr134a, htr136a, htr234a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd23a, hd68b, htr134a, htr136a, htr234a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd23a, hd69b, htr134a, htr136a, htr234a, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc356zy, htr136a, htr137a, htr367b, htr567a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr134a, htr137a, htr234a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr125a, htr258a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc356zy, htr136a, htr138a, htr368b, htr568a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr134a, htr138a, htr234a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc356zy, htr368c, htr389a, htr568a, htr689a]
          ·
            linarith only [hlam, hc356zy, htr368a, htr568b, htr589a, htr689a]
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hd12b, hd68a, htr025a, htr026a, htr125a, htr256b, htr568a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          rcases m.htr 2 6 7 (by decide) (by decide) with
            ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd36b, htr023a, htr026a, htr267a, htr367a]
          ·
            linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr567a, htr568a]
      ·
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr025a, htr026a, htr125a, htr256b, htr567a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hd23a, hd36b, htr023a, htr026a, htr268a, htr368a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hd23a, hd36b, htr023a, htr026a, htr269a, htr369a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr269a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr125a, htr256a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr125a, htr256a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr125a, htr256a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr134a, htr137a, htr234a, htr347c, htr478a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr379a, htr679a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
        ·
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr479a, htr7910a, htr8910a]
            ·
              linarith only [hlam, hc467zy, htr479c, htr4910a, htr679a, htr7910a]
          ·
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr134a, htr137a, htr234a, htr379a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr478a, htr479a]
            ·
              linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a]
    ·
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr026a, htr136a, htr236c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr025a, htr026a, htr125a, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr025a, htr026a, htr125a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hd12b, hd69a, htr025a, htr026a, htr125a, htr269a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd26a, hd35b, htr135a, htr136a, htr267a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd26a, hd35b, htr135a, htr136a, htr268a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd26a, hd35b, htr135a, htr136a, htr269a, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr236a, htr369a, htr467a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr234a, htr346a, htr469a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hd12b, hd910a, htr125a, htr258a, htr589a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr125a, htr259a, htr5910a, htr8910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc267yz, htr279a, htr679c, htr6910a, htr7910a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hd12b, hd79a, htr025a, htr027a, htr125a, htr279a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd23a, hd67b, htr023a, htr027a, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
            ·
              linarith only [hlam, hd12b, hd79a, htr127a, htr278a, htr578a, htr579a]
          ·
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]
            ·
              linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr579a, htr7910a, htr8910a]
        ·
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr025a, htr027a, htr125a, htr257b, htr578a])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr023a, htr027a, htr279a, htr679a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr127a, htr279a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12b, hd910a, htr125a, htr257a, htr579a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
      ·
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc246yz, htr026a, htr027a, htr267c, htr467a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr025a, htr027a, htr125a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc246yz, htr026a, htr028a, htr268c, htr468a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr025a, htr028a, htr125a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc246yz, htr268b, htr289a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a]
        ·
          linarith only [hlam, hd23a, hd78b, htr236a, htr368a, htr689a, htr789a]

theorem shard_126 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_126 m htr013a htr023a htr023b htr023c htr024a htr024b htr024c htr025a htr025b htr125a htr126a

#print axioms shard_126
end Jsp404.NoSatElevenDBMTerminal
