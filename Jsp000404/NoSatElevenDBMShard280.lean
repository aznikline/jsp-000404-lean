import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_280 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr149a : m.d 4 9 + lam ≤ m.d 1 4)
    (htr149b : m.d 4 9 < m.d 1 9)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  have hd49a := (m.hrange 4 9 (by decide)).1
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr015c, htr017b, htr057c])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr016c, htr017b, htr067c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr015b, htr057a, htr157a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc567xy, htr015a, htr017a, htr156a, htr157c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc578yx, htr015a, htr017a, htr157c, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, hc579yx, htr015a, htr017a, htr157c, htr159a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, htr016b, htr067a, htr167a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc678yx, htr016a, htr017a, htr167c, htr168a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hc679yx, htr016a, htr017a, htr167c, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc135yz, htr015a, htr017a, htr157c, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, htr146b, htr168a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, htr146b, htr169a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc156yz, htr016a, htr017a, htr167c, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 3 5 6 (by decide) (by decide) with
    ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
  ·
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd15a, hd67b, htr158a, htr356a, htr358a, htr567a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hd15a, hd67b, htr159a, htr356a, htr359a, htr567a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr135a, htr356a, htr567a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr178a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd13a, hd79b, htr135a, htr356a, htr567a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr179a, htr679a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr135a, htr356a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd13a, hd810b, htr135a, htr356a, htr568a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      rcases m.htr 5 6 9 (by decide) (by decide) with
        ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
      ·
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc123yx, hc678zy, htr124a, htr135a, htr247a, htr356a, htr478a, htr568a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc134xy, hc468yz, htr135a, htr147a, htr247a, htr248a, htr356a, htr568a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          rcases m.htr 4 8 9 (by decide) (by decide) with
            ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
          ·
            linarith only [hlam, hd45a, hd68b, htr245a, htr248a, htr489a, htr689a]
          ·
            linarith only [hlam, hc134xy, hc678zy, htr135a, htr148a, htr356a, htr489a, htr568a, htr789a]
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc134xy, hc689zy, htr135a, htr147a, htr356a, htr478a, htr569a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr245a, htr247a, htr478a, htr678a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc134xy, hc467yz, htr135a, htr148a, htr247a, htr248a, htr356a, htr567a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          rcases m.htr 4 8 9 (by decide) (by decide) with
            ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
          ·
            linarith only [hlam, hc137xy, hc468yz, htr135a, htr178a, htr356a, htr489a, htr568a, htr789a]
          ·
            linarith only [hlam, hc123yx, hc689zy, htr124a, htr135a, htr248a, htr356a, htr489a, htr569a]
      ·
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc456yz, htr149b, htr169c, htr246a, htr249a, htr569a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc467yz, htr479a, htr567a, htr569a, htr679b])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc678zy, htr568a, htr569a, htr689b, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr245a, htr247a, htr478a, htr678a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc134xy, hc467yz, htr135a, htr148a, htr247a, htr248a, htr356a, htr567a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr678c, htr6810a, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc137xy, hc468yz, htr135a, htr178a, htr356a, htr4810a, htr568a, htr7810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hc123yx, hc8910yz, htr124a, htr135a, htr248a, htr359a, htr4810a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc156yz, htr169a, htr569c, htr5910a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd67b, hd89a, htr567a, htr569a, htr6910a, htr8910a]
          ·
            linarith only [hlam, hd67b, hd910a, htr478a, htr479a, htr678a, htr789b, htr8910a]
        ·
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc123yx, hc678zy, htr124a, htr135a, htr247a, htr356a, htr478a, htr568a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc134xy, hc468yz, htr135a, htr147a, htr247a, htr248a, htr356a, htr568a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd45a, hd68b, htr245a, htr248a, htr4810a, htr6810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd14b, hd910a, htr147a, htr247a, htr249a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc456yz, htr469b, htr4910a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hc156yz, htr169a, htr569c, htr5910a, htr6910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hc134xy, hc678zy, htr135a, htr148a, htr356a, htr4810a, htr568a, htr7810a]
          ·
            linarith only [hlam, hc134xy, hc8910yz, htr135a, htr147a, htr359a, htr478a, htr5910a, htr7810a]
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc156yz, htr016a, htr018a, htr168c, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc456yz, htr148b, htr168c, htr246a, htr248a, htr568a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd13a, hd67b, htr136a, htr368a, htr567a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467yz, htr478a, htr567a, htr568a, htr678b])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 5 6 9 (by decide) (by decide) with
        ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr356c, htr369a, htr569a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, htr368c, htr369b, htr389c])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd13a, hd67b, htr138a, htr389a, htr567a, htr568c, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc123yx, hc8910yx, htr012a, htr018a, htr135a, htr1810a, htr358a, htr589a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc156yz, htr168b, htr1810a, htr568a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc156yz, htr168a, htr568c, htr5810a, htr6810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd13a, hd910b, htr135a, htr356a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hc123yx, hc679zy, htr124a, htr135a, htr247a, htr356a, htr479a, htr569a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, hc134xy, hc469yz, htr135a, htr147a, htr247a, htr249a, htr356a, htr569a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          rcases m.htr 4 9 10 (by decide) (by decide) with
            ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          ·
            linarith only [hlam, hd45a, hd69b, htr245a, htr249a, htr4910a, htr6910a]
          ·
            linarith only [hlam, hc134xy, hc679zy, htr135a, htr149a, htr356a, htr4910a, htr569a, htr7910a]
        ·
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc134xy, hc8910zy, htr135a, htr147a, htr358a, htr479a, htr5810a, htr7910a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr245a, htr247a, htr479a, htr679a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, hc134xy, hc467yz, htr135a, htr149a, htr247a, htr249a, htr356a, htr567a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          rcases m.htr 4 9 10 (by decide) (by decide) with
            ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          ·
            linarith only [hlam, hc137xy, hc469yz, htr135a, htr179a, htr356a, htr4910a, htr569a, htr7910a]
          ·
            linarith only [hlam, hc123yx, hc8910zy, htr124a, htr135a, htr249a, htr358a, htr4910a, htr5810a]
      ·
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc456yz, htr149b, htr169c, htr246a, htr249a, htr569a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc156yz, htr168a, htr368a, htr369a, htr569a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc467yz, htr479a, htr567a, htr569a, htr679b])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        rcases m.htr 5 6 10 (by decide) (by decide) with
          ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
        ·
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr356c, htr3610a, htr5610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr3610b, htr368c, htr3810c])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, htr3610b, htr369c, htr3910c])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, hd13a, hd67b, htr138a, htr3810a, htr567a, htr568c, htr5810a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc123yx, hc8910xy, htr012a, htr018a, htr135a, htr189a, htr358a, htr5810a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd13a, hd67b, htr139a, htr3910a, htr567a, htr569c, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc156yz, htr168b, htr189a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc156yz, htr168a, htr568c, htr589a, htr689a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd910b, htr135a, htr358a, htr589a, htr8910a]
          ·
            linarith only [hlam, hd13a, hd89b, htr135a, htr359a, htr5910a, htr8910a]
        ·
          rcases m.htr 2 4 7 (by decide) (by decide) with
            ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
          ·
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd14b, hd89a, htr147a, htr247a, htr248a, htr489a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc134xy, hc489yz, htr135a, htr147a, htr247a, htr249a, htr358a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            rcases m.htr 6 8 9 (by decide) (by decide) with
              ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
            ·
              linarith only [hlam, hc156yz, htr168a, htr568c, htr589a, htr689a]
            ·
              linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a]
          ·
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc123yx, hc789yz, htr124a, htr135a, htr247a, htr358a, htr479a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc156yz, htr168a, htr568c, htr589a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd67b, hd78a, htr567a, htr568a, htr689a, htr789a]
            ·
              linarith only [hlam, hd12b, hd89a, htr124a, htr247a, htr478a, htr789a]
  ·
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc135yz, htr156b, htr168a, htr356a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc135yz, htr156b, htr169a, htr356a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd15a, hd78b, htr156a, htr356a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd15a, hd79b, htr156a, htr356a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd13a, hd57b, htr013a, htr017a, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 2 4 7 (by decide) (by decide) with
      ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd45a, hd57b, htr245a, htr247a, htr478a, htr578a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd45a, hd57b, htr245a, htr247a, htr479a, htr579a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      rcases m.htr 3 5 8 (by decide) (by decide) with
        ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc145yx, hc458yz, htr147a, htr156a, htr247a, htr248a, htr356a, htr358a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd15a, hd89b, htr156a, htr356a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45a, hd58b, htr245a, htr248a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd15a, hd810b, htr156a, htr356a, htr358a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hd45a, hd58b, htr245a, htr248a, htr4810a, htr5810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc145yx, hc578zy, htr148a, htr156a, htr356a, htr358a, htr489a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc145yx, hc589zy, htr147a, htr156a, htr356a, htr359a, htr478a, htr789a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc345zy, htr149b, htr159c, htr245a, htr249a, htr359a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd14b, hd910a, htr147a, htr247a, htr249a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd49a, hd57b, htr357a, htr359a, htr4910a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc145yx, hc689zy, htr147a, htr159a, htr478a, htr5910a, htr6910a, htr789a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc145yx, hc578zy, htr148a, htr156a, htr356a, htr358a, htr4810a, htr7810a]
        ·
          linarith only [hlam, hc145yx, hc8910yz, htr147a, htr156a, htr478a, htr569a, htr6910a, htr7810a]
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc345zy, htr148b, htr158c, htr245a, htr248a, htr358a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd14b, hd89a, htr147a, htr247a, htr248a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hd14b, hd810a, htr147a, htr247a, htr248a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd48a, hd57b, htr357a, htr358a, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd48a, hd57b, htr357a, htr358a, htr4810a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc145yx, hc468yz, htr147a, htr158a, htr247a, htr248a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc145yx, hc489yz, htr147a, htr156a, htr247a, htr249a, htr568a, htr689a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc345zy, htr149b, htr159c, htr245a, htr249a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd15a, hd910b, htr156a, htr356a, htr359a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd45a, hd59b, htr245a, htr249a, htr4910a, htr5910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc145yx, hc468yz, htr147a, htr158a, htr247a, htr248a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc145yx, hc789yz, htr149a, htr156a, htr4910a, htr568a, htr689a, htr7910a]
        ·
          linarith only [hlam, hc145yx, hc8910zy, htr147a, htr156a, htr479a, htr568a, htr6810a, htr7910a]
    ·
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc145yx, hc457yz, htr148a, htr156a, htr247a, htr248a, htr356a, htr357a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr249a, htr249b, htr249c, _, _⟩
        linarith only [hlam, hc145yx, hc457yz, htr149a, htr156a, htr247a, htr249a, htr356a, htr357a])
      obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc457yz, htr357a, htr358a, htr478a, htr578b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd15a, hd89b, htr156a, htr356a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd15a, hd810b, htr156a, htr356a, htr358a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc457yz, htr478a, htr578c, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc457yz, htr478b, htr489a, htr578a, htr789a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc125yx, hc589zy, htr124a, htr156a, htr248a, htr356a, htr359a, htr489a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc457yz, htr478a, htr578c, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc457yz, htr478b, htr4810a, htr578a, htr7810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc125yx, hc8910yz, htr124a, htr156a, htr248a, htr4810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc125yx, hc689zy, htr124a, htr159a, htr248a, htr489a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd57b, hd89a, htr357a, htr359a, htr5910a, htr8910a]
        ·
          linarith only [hlam, hd12b, hd910a, htr124a, htr248a, htr489a, htr8910a]
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc125yx, hc578zy, htr124a, htr156a, htr247a, htr356a, htr358a, htr478a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc135yz, htr015a, htr018a, htr158c, htr358a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr124a, htr247a, htr478a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd57b, hd78a, htr357a, htr358a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc125yx, hc678zy, htr124a, htr158a, htr247a, htr478a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc125yx, hc8910yx, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc125yx, hc789yz, htr124a, htr156a, htr247a, htr479a, htr568a, htr689a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc457yz, htr357a, htr359a, htr479a, htr579b])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc135yz, htr158b, htr1810a, htr358a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd15a, hd910b, htr156a, htr356a, htr359a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc125yx, hc678zy, htr124a, htr158a, htr247a, htr478a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc125yx, hc8910zy, htr124a, htr156a, htr249a, htr4910a, htr568a, htr6810a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc457yz, htr479a, htr579c, htr5910a, htr7910a]
        ·
          linarith only [hlam, hc157xy, hc489yz, htr156a, htr179a, htr4910a, htr568a, htr689a, htr7910a]

theorem shard_280 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr149a : m.d 4 9 + lam ≤ m.d 1 4)
    (htr149b : m.d 4 9 < m.d 1 9)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    : False :=
  proof_shard_280 m htr012a htr013a htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr124a htr135a htr136a htr138a htr139a htr146b htr147a htr148a htr148b htr149a htr149b htr245a htr246a

#print axioms shard_280
end Jsp404.NoSatElevenDBMTerminal
