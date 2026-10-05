import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_284 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr056b : m.d 0 5 < m.d 0 6)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  have hd18a := (m.hrange 1 8 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
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
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  rcases m.htr 3 5 7 (by decide) (by decide) with
    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
  ·
    rcases m.htr 3 5 8 (by decide) (by decide) with
      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
    ·
      rcases m.htr 3 5 9 (by decide) (by decide) with
        ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
      ·
        rcases m.htr 3 5 10 (by decide) (by decide) with
          ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc123yx, hc678yx, htr012a, htr016a, htr135a, htr168a, htr356a, htr567a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc123yx, hc679yx, htr012a, htr016a, htr135a, htr169a, htr356a, htr567a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd13a, hd78b, htr135a, htr356a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd13a, hd79b, htr135a, htr356a, htr567a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc123yx, hc678zy, htr012a, htr017a, htr135a, htr178a, htr356a, htr568a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd13a, hd89b, htr135a, htr356a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd13a, hd810b, htr135a, htr356a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc167yz, htr178a, htr678c, htr689a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc167yz, htr178b, htr189a, htr678a, htr789a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc123yx, hc689zy, htr012a, htr018a, htr135a, htr189a, htr356a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc167yz, htr178a, htr678c, htr6810a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc167yz, htr178b, htr1810a, htr678a, htr7810a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                linarith only [hlam, hc123yx, hc8910yz, htr012a, htr018a, htr135a, htr1810a, htr359a, htr5910a])
              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc126yx, hc589zy, htr012a, htr018a, htr169a, htr189a, htr5910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd67b, hd89a, htr567a, htr569a, htr6910a, htr8910a]
              ·
                linarith only [hlam, hd12b, hd910a, htr012a, htr018a, htr189a, htr8910a]
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc167yz, htr178a, htr567a, htr568a, htr678b])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd13a, hd67b, htr136a, htr368a, htr567a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd67b, hd78a, htr567a, htr568a, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc123yx, hc789yz, htr012a, htr017a, htr135a, htr179a, htr358a, htr589a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc123yx, hc8910yx, htr012a, htr018a, htr135a, htr1810a, htr358a, htr589a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc167yz, htr179a, htr356c, htr369a, htr567a, htr679b])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd18a, hd67b, htr1810a, htr567a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                linarith only [hlam, hc678yx, htr567a, htr568c, htr5810a, htr6810a])
              obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc123yx, hc8910zy, htr012a, htr019a, htr135a, htr1910a, htr358a, htr5810a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd16a, hd910b, htr168a, htr368a, htr369a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc167yz, htr179a, htr679c, htr6910a, htr7910a]
              ·
                linarith only [hlam, hc167yz, htr179b, htr1910a, htr679a, htr7910a]
          ·
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr167a, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd13a, hd68b, htr136a, htr367a, htr567a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                rcases m.htr 4 6 8 (by decide) (by decide) with
                  ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc456yz, htr067a, htr068a, htr468a, htr567a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc456yz, htr367a, htr368a, htr468a, htr567a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  rcases m.htr 4 6 9 (by decide) (by decide) with
                    ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                  ·
                    rcases m.htr 4 6 10 (by decide) (by decide) with
                      ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                    ·
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc123yx, hc789yx, htr012a, htr017a, htr136a, htr179a, htr367a, htr678a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc456yz, htr147b, htr179a, htr367c, htr379a, htr467b, htr567a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd13a, hd78b, htr137a, htr379a, htr578a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc123yx, hc789zy, htr012a, htr018a, htr135a, htr189a, htr357a, htr579a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc456yz, htr148b, htr189a, htr468b, htr568a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd13a, hd89b, htr136a, htr367a, htr678a, htr789a]
                        ·
                          linarith only [hlam, hd13a, hd78b, htr136a, htr368a, htr689a, htr789a]
                      ·
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hc456yz, htr147b, htr178a, htr467b, htr567a, htr678a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hc123yx, hc789xy, htr012a, htr017a, htr136a, htr178a, htr367a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc456yz, htr147b, htr179a, htr467b, htr567a, htr679a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc123yx, hc789yz, htr012a, htr017a, htr135a, htr179a, htr358a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc123yx, hc578zy, htr012a, htr017a, htr138a, htr178a, htr389a, htr589a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc456yz, htr148b, htr189a, htr368c, htr389a, htr468b, htr568a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr189a, htr789a]
                        ·
                          linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a]
                    ·
                      have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                        linarith only [hlam, htr046b, htr0610a, htr4610a])
                      obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr0610c, htr067b, htr0710b])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0610c, htr068b, htr0810b])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                        linarith only [hlam, hc127yx, htr012a, htr017c, htr0710a, htr1710a])
                      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hc128yx, htr012a, htr018c, htr0810a, htr1810a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc123yx, hc7810yx, htr012a, htr017a, htr136a, htr1710a, htr367a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc456yz, htr147b, htr178a, htr467b, htr567a, htr678a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr1810a, htr7810a]
                      ·
                        linarith only [hlam, hd12b, hd810a, htr012a, htr017a, htr178a, htr7810a]
                  ·
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, htr046b, htr069a, htr469a])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr067b, htr069c, htr079b])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr068b, htr069c, htr089b])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hc127yx, htr012a, htr017c, htr079a, htr179a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc128yx, htr012a, htr018c, htr089a, htr189a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc123yx, hc789yx, htr012a, htr017a, htr136a, htr179a, htr367a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc456yz, htr147b, htr178a, htr467b, htr567a, htr678a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr189a, htr789a]
                    ·
                      linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a]
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, htr046b, htr068a, htr468a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr067b, htr068c, htr078b])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, htr136c, htr146b, htr368a, htr468a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc123yx, hc789xy, htr012a, htr017a, htr136a, htr178a, htr367a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr179a, htr467b, htr567a, htr679a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc123yx, hc789yz, htr012a, htr017a, htr135a, htr179a, htr358a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc123yx, hc568zy, htr012a, htr016a, htr138a, htr146b, htr389a, htr468a, htr589a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd56b, hd78a, htr367a, htr368c, htr389a, htr567a, htr789a]
                  ·
                    linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a]
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc123yx, hc789yx, htr012a, htr017a, htr135a, htr179a, htr357a, htr578a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc123yx, hc7810yx, htr012a, htr017a, htr135a, htr1710a, htr357a, htr578a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr179a, htr467b, htr567a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc123yx, hc789zy, htr012a, htr018a, htr135a, htr189a, htr357a, htr579a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr1710a, htr467b, htr567a, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr5710a, htr6710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                    linarith only [hlam, hc123yx, hc7910zy, htr012a, htr019a, htr135a, htr1910a, htr357a, htr5710a])
                  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd13a, hd89b, htr135a, htr357a, htr578a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd13a, hd910b, htr135a, htr357a, htr579a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc178yz, htr189a, htr789c, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc178yz, htr189b, htr1910a, htr789a, htr8910a]
                ·
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr178a, htr467b, htr567a, htr678a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc123yx, hc789xy, htr012a, htr017a, htr135a, htr178a, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hc123yx, hc7810xy, htr012a, htr017a, htr135a, htr178a, htr357a, htr5710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr179a, htr467b, htr567a, htr679a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc123yx, hc789yz, htr012a, htr017a, htr135a, htr179a, htr358a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr5710a, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr1710a, htr467b, htr567a, htr6710a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hc123yx, hc7910yz, htr012a, htr017a, htr135a, htr1710a, htr359a, htr5910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd12b, hd910a, htr012a, htr017a, htr179a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
            ·
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc123yx, hc678xy, htr012a, htr016a, htr135a, htr146b, htr356a, htr467a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr146b, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd12b, hd79a, htr012a, htr016a, htr146b, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr179a, htr679a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yz, htr012a, htr016a, htr135a, htr168a, htr357a, htr578a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc126yx, htr012a, htr016c, htr068a, htr168a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd13a, hd89b, htr135a, htr357a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd67a, hd78b, htr146b, htr168a, htr467a, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc678xy, htr146b, htr168b, htr189a, htr467a, htr689a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc123yx, hc789zy, htr012a, htr018a, htr135a, htr189a, htr357a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc567zy, htr046b, htr069a, htr467a, htr579a, htr679c])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc8910xy, htr068a, htr069a, htr6810a, htr689b])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc678xy, htr146b, htr168b, htr1810a, htr467a, htr6810a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                  linarith only [hlam, hc123yx, hc8910yz, htr012a, htr018a, htr135a, htr1810a, htr359a, htr5910a])
                obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd56b, hd910a, htr068a, htr069a, htr568a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc127yx, hc589zy, htr012a, htr018a, htr179a, htr189a, htr5910a, htr7910a]
                ·
                  linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
              ·
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc567zy, htr146b, htr168a, htr467a, htr578a, htr678c])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr168a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd12b, hd810a, htr012a, htr016a, htr168a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, hc123yx, hc689yz, htr012a, htr016a, htr135a, htr169a, htr358a, htr589a])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  linarith only [hlam, hc567zy, htr578a, htr678b, htr6810a, htr7810a])
                obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                  linarith only [hlam, hc567zy, htr578c, htr5810a, htr678a, htr7810a])
                obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc123yx, hc8910zy, htr012a, htr019a, htr135a, htr1910a, htr358a, htr5810a])
                obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hc679xy, htr146b, htr169b, htr1910a, htr467a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd910b, htr135a, htr358a, htr589a, htr8910a]
                ·
                  linarith only [hlam, hd67a, hd89b, htr146b, htr169a, htr467a, htr6910a, htr8910a]
        ·
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr3510c, htr356b, htr3610b])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr3510c, htr357b, htr3710b])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, htr356c, htr3610a, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
            linarith only [hlam, hc156yz, htr1610a, htr3510a, htr356a, htr5610b])
          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc6710yx, htr3510a, htr356a, htr5610b, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, htr357c, htr3710a, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
            linarith only [hlam, hc157yz, htr1710a, htr3510a, htr357a, htr5710b])
          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc7810yx, htr3510a, htr357a, htr5710b, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc567zy, htr3510a, htr357a, htr5710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hd12b, hd710a, htr012a, htr016a, htr167a, htr6710a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, hc5610yx, htr0510a, htr056b, htr067a, htr567a])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc123yx, hc578zy, htr012a, htr013b, htr017a, htr035b, htr0510a, htr178a, htr3510a, htr358a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd57b, hd610a, htr1610a, htr167a, htr578a, htr678a]
          ·
            linarith only [hlam, hd56b, hd710a, htr1710a, htr178a, htr567a, htr678a]
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr356b, htr359c, htr369b])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr357b, htr359c, htr379b])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, htr356c, htr369a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hc156yz, htr169a, htr356a, htr359a, htr569b])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc679yx, htr356a, htr359a, htr567a, htr569b])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, htr357c, htr379a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc157yz, htr179a, htr357a, htr359a, htr579b])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc789yx, htr357a, htr359a, htr578a, htr579b])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc567zy, htr357a, htr359a, htr579b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr012a, htr016a, htr167a, htr679a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc569yx, htr056b, htr059a, htr067a, htr567a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc123yx, hc578zy, htr012a, htr013b, htr017a, htr035b, htr059a, htr178a, htr358a, htr359a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd57b, hd69a, htr167a, htr169a, htr578a, htr678a]
        ·
          linarith only [hlam, hd56b, hd79a, htr178a, htr179a, htr567a, htr678a]
    ·
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr356b, htr358c, htr368b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr357b, htr358c, htr378b])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, htr356c, htr368a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc156yz, htr168a, htr356a, htr358a, htr568b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc678yx, htr356a, htr358a, htr567a, htr568b])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc689xy, htr356a, htr358a, htr568b, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, htr357c, htr378a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc157yz, htr178a, htr357a, htr358a, htr578b])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc789xy, htr357a, htr358a, htr578b, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hc7810xy, htr357a, htr358a, htr5710a, htr578b])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc567zy, htr357a, htr358a, htr578b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc569yx, htr058a, htr059a, htr356a, htr358a])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd57b, hd68a, htr167a, htr168a, htr579a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hd56b, hd78a, htr178a, htr179a, htr567a, htr679a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr359a, htr359b, htr359c, _, _⟩
        linarith only [hlam, hc123yx, hc579zy, htr012a, htr013b, htr017a, htr035b, htr058a, htr179a, htr358a, htr359a])
      obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc056yz, htr069a, htr356a, htr359a, htr569b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hd57b, hd68a, htr167a, htr168a, htr5710a, htr6710a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
        linarith only [hlam, hd56b, hd78a, htr1710a, htr178a, htr567a, htr6710a])
      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd56b, hd68a, htr356a, htr358a, htr589a, htr689a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd56b, hd910a, htr067a, htr069a, htr567a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd56b, hd69a, htr356a, htr359a, htr5910a, htr6910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc123yx, hc7910yz, htr012a, htr013b, htr017a, htr035b, htr058a, htr1710a, htr589a, htr8910a]
      ·
        linarith only [hlam, hc123yx, hc789yz, htr012a, htr013b, htr017a, htr035b, htr059a, htr179a, htr5910a, htr8910a]
  ·
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr356b, htr357c, htr367b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, htr356c, htr367a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc156yz, htr167a, htr356a, htr357a, htr567b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc456yz, htr356a, htr357a, htr467a, htr567b])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc678xy, htr356a, htr357a, htr567b, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc567yx, htr356b, htr357a, htr368a, htr568a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc679xy, htr356a, htr357a, htr567b, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr578a, htr678a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc567yx, htr356a, htr357c, htr378a, htr578a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd12b, hd79a, htr012a, htr016a, htr167a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr579a, htr679a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hc567yx, htr356a, htr357c, htr379a, htr579a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr157a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      rcases m.htr 4 6 8 (by decide) (by decide) with
        ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr012a, htr016c, htr068a, htr467a, htr468a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc456yz, htr356a, htr358a, htr468a, htr568b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45a, hd89b, htr357a, htr358a, htr457a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd45a, hd810b, htr357a, htr358a, htr457a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd58b, hd67a, htr467a, htr468a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc678xy, htr148b, htr189a, htr467a, htr468b, htr689a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc125yx, hc589zy, htr012a, htr018a, htr157a, htr189a, htr357a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, hc056yz, htr069a, htr356a, htr359a, htr569b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd58b, hd67a, htr467a, htr468a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc678xy, htr148b, htr1810a, htr467a, htr468b, htr6810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd56b, hd910a, htr068a, htr069a, htr568a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd56b, hd69a, htr356a, htr359a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc123yx, hc8910yz, htr012a, htr018a, htr137a, htr1810a, htr379a, htr7910a]
        ·
          linarith only [hlam, hc125yx, hc789zy, htr012a, htr018a, htr157a, htr189a, htr579b, htr5910a, htr7910a]
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc125yx, hc568zy, htr012a, htr016a, htr146b, htr157a, htr357a, htr358a, htr468a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr146b, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd56b, hd68a, htr356a, htr358a, htr589a, htr689a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd12b, hd810a, htr012a, htr016a, htr146b, htr468a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd56b, hd68a, htr356a, htr358a, htr5810a, htr6810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc125yx, hc678yz, htr012a, htr016a, htr146b, htr157a, htr468a, htr578b, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hc123yx, hc689yz, htr012a, htr016a, htr137a, htr169a, htr378a, htr789a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc156yz, htr169a, htr356a, htr359a, htr569b])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd45a, hd910b, htr357a, htr359a, htr457a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd59b, hd67a, htr167a, htr169a, htr5910a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc679xy, htr167a, htr169b, htr1910a, htr6910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc123yx, hc8910zy, htr012a, htr019a, htr137a, htr1910a, htr378a, htr7810a]
        ·
          linarith only [hlam, hc125yx, hc678yz, htr012a, htr016a, htr146b, htr157a, htr468a, htr578b, htr5810a, htr7810a]
    ·
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc567yx, htr146b, htr168a, htr456b, htr457a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc567yx, htr146b, htr169a, htr456b, htr457a, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, hc128yx, htr012a, htr018c, htr089a, htr189a])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc123yx, hc689yz, htr012a, htr016a, htr137a, htr169a, htr378a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc123yx, hc678yz, htr012a, htr016a, htr138a, htr168a, htr389a, htr789a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567yx, htr045b, htr058b, htr089a, htr356c, htr368c, htr389a, htr457a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      rcases m.htr 3 5 8 (by decide) (by decide) with
        ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
      ·
        linarith only [hlam, htr035c, htr058a, htr358a]
      ·
        linarith only [hlam, hc128yx, hc567yx, htr012a, htr015a, htr145b, htr189a, htr356a, htr358c, htr389a, htr457a]

theorem shard_284 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr056b : m.d 0 5 < m.d 0 6)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    : False :=
  proof_shard_284 m htr012a htr013b htr015a htr016a htr016c htr017a htr017c htr018a htr018c htr019a htr035b htr035c htr045b htr046b htr056b htr135a htr136a htr136c htr137a htr138a htr145b htr146b htr147b htr148b htr356a htr356b htr356c htr456b

#print axioms shard_284
end Jsp404.NoSatElevenDBMTerminal
