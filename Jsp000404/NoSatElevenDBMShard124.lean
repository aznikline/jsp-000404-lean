import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_124 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
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
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
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
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc269xy, hc269yx, hc269yz, hc269zy⟩ := endpoint_caps m 2 6 9 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr024b, htr025c, htr045b])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
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
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr024a, htr025a, htr124a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd12b, hd57a, htr024a, htr025a, htr124a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr024a, htr025a, htr124a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, hd12b, hd59a, htr024a, htr025a, htr124a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, hd12b, hd510a, htr024a, htr025a, htr124a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  rcases m.htr 0 2 6 (by decide) (by decide) with
    ⟨htr026a, htr026b, htr026c, _, _⟩ | ⟨htr026a, htr026b, htr026c, _, _⟩
  ·
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hc123zy, htr023a, htr026a, htr136a, htr236c])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc235yz, htr025a, htr026a, htr256c, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 1 3 5 (by decide) (by decide) with
      ⟨htr135a, htr135b, htr135c, _, _⟩ | ⟨htr135a, htr135b, htr135c, _, _⟩
    ·
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hd23a, hd56b, htr135a, htr137a, htr237a, htr356a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr013a, htr135a, htr356a, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd23a, hd56b, htr023a, htr026a, htr267a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd01a, hd68b, htr013a, htr135a, htr356a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd23a, hd56b, htr023a, htr026a, htr268a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hd01a, hd69b, htr013a, htr135a, htr356a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hd23a, hd56b, htr023a, htr026a, htr269a, htr569a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc456yz, htr356a, htr357a, htr467a, htr567b])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc456yz, htr356a, htr358a, htr468a, htr568b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd01a, hd78b, htr013a, htr135a, htr357a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01a, hd89b, htr013a, htr135a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc456yz, htr468a, htr568c, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd12b, hd78a, htr126a, htr268a, htr689a, htr789a]
        ·
          linarith only [hlam, hd12b, hd89a, htr126a, htr267a, htr678a, htr789a]
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr269a, htr467a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr124a, htr246a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr124a, htr246a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr124a, htr246a, htr469a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 3 5 7 (by decide) (by decide) with
          ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
        ·
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd01a, hd78b, htr013a, htr135a, htr357a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc567zy, htr357a, htr358a, htr578b, htr678a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr013a, htr135a, htr358a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
          ·
            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
        ·
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr578a, htr678a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc235yz, htr257a, htr357c, htr378a, htr578a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr579a, htr679a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc235yz, htr257a, htr357c, htr379a, htr579a])
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
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr257a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr258a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr359a, htr359b, htr359c, _, _⟩
        linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr259a, htr359a])
      obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr135a, htr136a, htr235a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd23a, hd36b, htr023a, htr026a, htr267a, htr367a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd23a, hd68b, htr135a, htr136a, htr235a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd23a, hd36b, htr023a, htr026a, htr268a, htr368a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd23a, hd69b, htr135a, htr136a, htr235a, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hd23a, hd36b, htr023a, htr026a, htr269a, htr369a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc346zy, htr136a, htr137a, htr367b, htr467a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr135a, htr137a, htr235a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc346zy, htr136a, htr138a, htr368b, htr468a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr135a, htr138a, htr235a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc346zy, htr368c, htr389a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd12b, hd78a, htr126a, htr268a, htr689a, htr789a]
        ·
          linarith only [hlam, hd12b, hd89a, htr126a, htr267a, htr678a, htr789a]
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr126a, htr269a, htr467a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr124a, htr246a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr124a, htr246a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr124a, htr246a, htr469a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr135a, htr137a, htr235a, htr357c, htr578a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd34b, hd67a, htr134a, htr137a, htr379a, htr679a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr235a, htr357a, htr579a, htr7910a])
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
            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr235a, htr358a, htr589a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr235a, htr359a, htr5910a, htr8910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr579a, htr7910a, htr8910a]
            ·
              linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a]
          ·
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr135a, htr137a, htr235a, htr379a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd34b, hd67a, htr134a, htr137a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr578a, htr579a]
            ·
              linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr024a, htr026a, htr124a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr024a, htr026a, htr124a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd12b, hd69a, htr024a, htr026a, htr124a, htr269a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, hd12b, hd610a, htr024a, htr026a, htr124a, htr2610a])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    rcases m.htr 0 2 7 (by decide) (by decide) with
      ⟨htr027a, htr027b, htr027c, _, _⟩ | ⟨htr027a, htr027b, htr027c, _, _⟩
    ·
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc123zy, htr023a, htr027a, htr137a, htr237c])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc235yz, htr025a, htr027a, htr257c, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc236yz, htr026a, htr027a, htr267c, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc256yz, htr026a, htr027a, htr267c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 3 5 6 (by decide) (by decide) with
        ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
      ·
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hd01a, hd67b, htr013a, htr135a, htr356a, htr567a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr135a, htr136a, htr235a, htr367a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd26a, hd34b, htr134a, htr136a, htr268a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hd26a, hd34b, htr134a, htr136a, htr269a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr135a, htr137a, htr235a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd23a, hd37b, htr023a, htr027a, htr278a, htr378a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd23a, hd79b, htr135a, htr137a, htr235a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd23a, hd37b, htr023a, htr027a, htr279a, htr379a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr236a, htr369a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, htr367c, htr378a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, htr367c, htr379a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr235a, htr356a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr235a, htr356a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr127a, htr279a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12b, hd910a, htr124a, htr247a, htr479a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr124a, htr247a, htr478a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd12b, hd79a, htr127a, htr278a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd89a, htr127a, htr279a, htr7910a, htr8910a]
          ·
            linarith only [hlam, hd12b, hd910a, htr127a, htr278a, htr789a, htr8910a]
      ·
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr256a, htr356a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd23a, hd57b, htr135a, htr136a, htr236a, htr357a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc235yz, htr256b, htr268a, htr356a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd25a, hd67b, htr256a, htr367a, htr368a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc235yz, htr256b, htr269a, htr356a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hd25a, hd67b, htr256a, htr367a, htr369a, htr569a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd25a, hd78b, htr256a, htr356a, htr357a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd23a, hd57b, htr023a, htr027a, htr278a, htr578a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd25a, hd79b, htr256a, htr356a, htr357a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd23a, hd57b, htr023a, htr027a, htr279a, htr579a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, htr567c, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, htr567c, htr579a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd01a, hd910b, htr013a, htr136a, htr369a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr127a, htr279a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12b, hd910a, htr124a, htr247a, htr479a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr124a, htr247a, htr478a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd12b, hd79a, htr127a, htr278a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd89a, htr127a, htr279a, htr7910a, htr8910a]
          ·
            linarith only [hlam, hd12b, hd910a, htr127a, htr278a, htr789a, htr8910a]
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr024a, htr027a, htr124a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd12b, hd79a, htr024a, htr027a, htr124a, htr279a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hd12b, hd710a, htr024a, htr027a, htr124a, htr2710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      rcases m.htr 0 2 8 (by decide) (by decide) with
        ⟨htr028a, htr028b, htr028c, _, _⟩ | ⟨htr028a, htr028b, htr028c, _, _⟩
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc235yz, htr025a, htr028a, htr258c, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc236yz, htr026a, htr028a, htr268c, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
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
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr256a, htr356a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hd23a, hd58b, htr135a, htr136a, htr236a, htr358a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a]
          ·
            linarith only [hlam, hd25a, hd68b, htr256a, htr367a, htr368a, htr567a]
        ·
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr135a, htr135b, htr135c, _, _⟩
            linarith only [hlam, hd01a, hd68b, htr013a, htr135a, htr356a, htr568a])
          obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hd23a, hd68b, htr135a, htr136a, htr235a, htr368a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr567a, htr568a]
          ·
            linarith only [hlam, hd26a, hd34b, htr134a, htr136a, htr267a, htr367a]
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr024a, htr028a, htr124a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 0 2 9 (by decide) (by decide) with
          ⟨htr029a, htr029b, htr029c, _, _⟩ | ⟨htr029a, htr029b, htr029c, _, _⟩
        ·
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc126zy, htr026a, htr029a, htr169a, htr269c])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, hc235yz, htr025a, htr029a, htr259c, htr359a])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, hc236yz, htr026a, htr029a, htr269c, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc256yz, htr026a, htr029a, htr269c, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc267yz, htr027a, htr029a, htr279c, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc268yz, htr028a, htr029a, htr289c, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hd25a, hd69b, htr167a, htr169a, htr256a, htr567a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hd26a, hd79b, htr167a, htr168a, htr268a, htr679a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr235a, htr356a, htr567a, htr679a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr135a, htr135b, htr135c, _, _⟩
              linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr256a, htr356a])
            obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
            have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr136a, htr136b, htr136c, _, _⟩
              linarith only [hlam, hd23a, hd59b, htr135a, htr136a, htr236a, htr359a])
            obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
            rcases m.htr 3 6 8 (by decide) (by decide) with
              ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
            ·
              linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a]
            ·
              linarith only [hlam, hd01a, hd69b, htr016a, htr168a, htr368a, htr369a]
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hd01a, hd69b, htr016a, htr167a, htr567a, htr569a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hd26a, hd89b, htr167a, htr168a, htr267a, htr689a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr135a, htr135b, htr135c, _, _⟩
              linarith only [hlam, hd01a, hd69b, htr013a, htr135a, htr356a, htr569a])
            obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
            have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr136a, htr136b, htr136c, _, _⟩
              linarith only [hlam, hd23a, hd69b, htr135a, htr136a, htr235a, htr369a])
            obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
            rcases m.htr 3 6 8 (by decide) (by decide) with
              ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd69b, htr168a, htr169a, htr236a, htr368a]
            ·
              linarith only [hlam, hd26a, hd34b, htr134a, htr136a, htr268a, htr368a]
        ·
          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
            linarith only [hlam, hd12b, hd910a, htr024a, htr029a, htr124a, htr2910a])
          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
          rcases m.htr 0 2 10 (by decide) (by decide) with
            ⟨htr0210a, htr0210b, htr0210c, _, _⟩ | ⟨htr0210a, htr0210b, htr0210c, _, _⟩
          ·
            have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
              linarith only [hlam, hc126zy, htr0210a, htr026a, htr1610a, htr2610c])
            obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
            have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
              linarith only [hlam, hc235yz, htr0210a, htr025a, htr2510c, htr3510a])
            obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, hc236yz, htr0210a, htr026a, htr2610c, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc256yz, htr0210a, htr026a, htr2610c, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc267yz, htr0210a, htr027a, htr2710c, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc269yz, htr0210a, htr029a, htr2910c, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hd25a, hd610b, htr1610a, htr167a, htr256a, htr567a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hd26a, hd710b, htr167a, htr169a, htr269a, htr6710a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hd23a, hd710b, htr235a, htr356a, htr567a, htr6710a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr135a, htr135b, htr135c, _, _⟩
                linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr256a, htr356a])
              obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
              have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr136a, htr136b, htr136c, _, _⟩
                linarith only [hlam, hd23a, hd510b, htr135a, htr136a, htr236a, htr3510a])
              obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
              rcases m.htr 3 6 9 (by decide) (by decide) with
                ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd910b, htr013a, htr136a, htr369a, htr6910a]
              ·
                linarith only [hlam, hd01a, hd610b, htr016a, htr169a, htr3610a, htr369a]
            ·
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hd01a, hd610b, htr016a, htr167a, htr5610a, htr567a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hd26a, hd910b, htr167a, htr169a, htr267a, htr6910a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr135a, htr135b, htr135c, _, _⟩
                linarith only [hlam, hd01a, hd610b, htr013a, htr135a, htr356a, htr5610a])
              obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
              have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr136a, htr136b, htr136c, _, _⟩
                linarith only [hlam, hd23a, hd610b, htr135a, htr136a, htr235a, htr3610a])
              obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
              rcases m.htr 3 6 9 (by decide) (by decide) with
                ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd610b, htr1610a, htr169a, htr236a, htr369a]
              ·
                linarith only [hlam, hd26a, hd34b, htr134a, htr136a, htr269a, htr369a]
          ·
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                  linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
                obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
                have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr135a, htr135b, htr135c, _, _⟩
                  linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr256a, htr356a])
                obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
                have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr136a, htr136b, htr136c, _, _⟩
                  linarith only [hlam, hc235yz, htr135a, htr136a, htr256a, htr356b])
                obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
                rcases m.htr 3 6 7 (by decide) (by decide) with
                  ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                ·
                  linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a]
                ·
                  linarith only [hlam, hc235yz, htr256a, htr356c, htr367a, htr567a]
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc236yz, htr267b, htr278a, htr367a, htr678a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc267yz, htr278a, htr367a, htr368a, htr678b])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc267yz, htr278a, htr567a, htr568a, htr678b])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc267yz, htr278b, htr289a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc267yz, htr278a, htr368c, htr389a, htr678c, htr789a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc267yz, htr278a, htr678c, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr136a, htr136b, htr136c, _, _⟩
                  linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
                obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
                have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr138a, htr138b, htr138c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr136a, htr138a, htr236a, htr389a])
                obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
                have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr235a, htr356a, htr568a, htr689a])
                obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
                rcases m.htr 1 3 5 (by decide) (by decide) with
                  ⟨htr135a, htr135b, htr135c, _, _⟩ | ⟨htr135a, htr135b, htr135c, _, _⟩
                ·
                  linarith only [hlam, hc235yz, htr135a, htr138a, htr256a, htr356b, htr368b]
                ·
                  linarith only [hlam, hd25a, hd34b, htr134a, htr135a, htr256a, htr356a]
            ·
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hc125zy, htr156a, htr256b, htr267a, htr567a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc256yz, htr156a, htr157a, htr267a, htr567b])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc256yz, htr267a, htr356a, htr357a, htr567b])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc256yz, htr267b, htr278a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc256yz, htr267a, htr357c, htr378a, htr567c, htr678a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc256yz, htr267a, htr567c, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr135a, htr135b, htr135c, _, _⟩
                linarith only [hlam, hd01a, hd78b, htr013a, htr135a, htr357a, htr578a])
              obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
              have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr137a, htr137b, htr137c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr135a, htr137a, htr235a, htr378a])
              obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hd27a, hd34b, htr134a, htr137a, htr279a, htr379a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr578a, htr579a])
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
                linarith only [hlam, hc278yz, htr289a, htr789c, htr7910a, htr8910a]
              ·
                linarith only [hlam, hc278yz, htr289b, htr2910a, htr789a, htr8910a]

theorem shard_124 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    : False :=
  proof_shard_124 m htr013a htr015a htr016a htr023a htr024a htr024b htr024c htr025a htr025c htr124a htr126a htr127a htr134a htr235a htr236a htr236c htr237a htr237c

#print axioms shard_124
end Jsp404.NoSatElevenDBMTerminal
