import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_368 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr139c : m.d 1 9 < m.d 3 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < 4*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc369xy, hc369yx, hc369yz, hc369zy⟩ := endpoint_caps m 3 6 9 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr014b, htr017c, htr047b])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr015b, htr017c, htr057b])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr016b, htr017c, htr067b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, htr014c, htr047a, htr147a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc457yx, htr014a, htr017a, htr145a, htr147b])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc467yx, htr014a, htr017a, htr146a, htr147b])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hc478xy, htr014a, htr017a, htr147b, htr148a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr015c, htr057a, htr157a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc567yx, htr015a, htr017a, htr156a, htr157b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc578xy, htr015a, htr017a, htr157b, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, hc579xy, htr015a, htr017a, htr157b, htr159a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, htr016c, htr067a, htr167a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc678xy, htr016a, htr017a, htr167b, htr168a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hc679xy, htr016a, htr017a, htr167b, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, htr135c, htr158a, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, htr135c, htr159a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, htr136c, htr168a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, htr136c, htr169a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc145zy, htr015a, htr017a, htr157b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc156zy, htr016a, htr017a, htr167b, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc145zy, htr156c, htr168a, htr456a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc145zy, htr156c, htr169a, htr456a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd15b, hd78a, htr156a, htr456a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd14b, hd57a, htr014a, htr017a, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd15b, hd79a, htr156a, htr456a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd14b, hd57a, htr014a, htr017a, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc145zy, htr015a, htr018a, htr158b, htr458a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc345zy, htr138c, htr158b, htr235a, htr238a, htr458a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc357zy, htr378a, htr457a, htr458a, htr578c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 2 3 7 (by decide) (by decide) with
        ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
      ·
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc135xy, hc357zy, htr139a, htr156a, htr237a, htr239a, htr456a, htr457a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd57a, hd78b, htr457a, htr458a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc125xy, hc678yz, htr123a, htr158a, htr237a, htr378a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc125xy, hc789zy, htr123a, htr156a, htr237a, htr379a, htr568a, htr689a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc357zy, htr379a, htr457a, htr459a, htr579c])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc145zy, htr158c, htr1810a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd15b, hd910a, htr156a, htr456a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc125xy, hc678yz, htr123a, htr158a, htr237a, htr378a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hc125xy, hc8910yz, htr123a, htr156a, htr239a, htr3910a, htr568a, htr6810a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc157yx, hc389zy, htr156a, htr179a, htr3910a, htr568a, htr689a, htr7910a]
        ·
          linarith only [hlam, hc357zy, htr379a, htr579b, htr5910a, htr7910a]
      ·
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr379a, htr579a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr137a, htr237a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd13a, hd810b, htr137a, htr237a, htr238a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc345zy, htr358c, htr389a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc345zy, htr358c, htr3810a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc135xy, hc368zy, htr137a, htr158a, htr237a, htr238a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc135xy, hc389zy, htr137a, htr156a, htr237a, htr239a, htr568a, htr689a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc345zy, htr139c, htr159b, htr235a, htr239a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd15b, hd910a, htr156a, htr456a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd34b, hd59a, htr234a, htr239a, htr3910a, htr5910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc135xy, hc368zy, htr137a, htr158a, htr237a, htr238a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc135xy, hc8910yz, htr137a, htr156a, htr379a, htr568a, htr6810a, htr7910a]
        ·
          linarith only [hlam, hc135xy, hc789zy, htr139a, htr156a, htr3910a, htr568a, htr689a, htr7910a]
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd15b, hd89a, htr156a, htr456a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        linarith only [hlam, hd15b, hd810a, htr156a, htr456a, htr458a, htr5810a])
      obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
      rcases m.htr 2 3 7 (by decide) (by decide) with
        ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
      ·
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc135xy, hc357zy, htr138a, htr156a, htr237a, htr238a, htr456a, htr457a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc125xy, hc578yz, htr123a, htr156a, htr237a, htr378a, htr456a, htr458a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc357zy, htr378a, htr578b, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc157yx, hc358zy, htr156a, htr178a, htr389a, htr456a, htr458a, htr789a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc125xy, hc589yz, htr123a, htr156a, htr238a, htr389a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc357zy, htr378a, htr578b, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hc157yx, hc358zy, htr156a, htr178a, htr3810a, htr456a, htr458a, htr7810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc125xy, hc8910zy, htr123a, htr156a, htr238a, htr3810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc125xy, hc689yz, htr123a, htr159a, htr238a, htr389a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd910b, htr123a, htr238a, htr389a, htr8910a]
        ·
          linarith only [hlam, hd57a, hd89b, htr457a, htr459a, htr5910a, htr8910a]
      ·
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc135xy, hc358zy, htr137a, htr156a, htr237a, htr238a, htr456a, htr458a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd34b, hd58a, htr234a, htr238a, htr389a, htr589a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd34b, hd58a, htr234a, htr238a, htr3810a, htr5810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc135xy, hc578yz, htr138a, htr156a, htr389a, htr456a, htr458a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc135xy, hc589yz, htr137a, htr156a, htr378a, htr456a, htr459a, htr789a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc345zy, htr139c, htr159b, htr235a, htr239a, htr459a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd13a, hd910b, htr137a, htr237a, htr239a, htr3910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc345zy, htr359c, htr3910a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc135xy, hc689yz, htr137a, htr159a, htr378a, htr5910a, htr6910a, htr789a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc135xy, hc8910zy, htr137a, htr156a, htr378a, htr569a, htr6910a, htr7810a]
        ·
          linarith only [hlam, hc135xy, hc578yz, htr138a, htr156a, htr3810a, htr456a, htr458a, htr7810a]
  ·
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd15b, hd67a, htr158a, htr456a, htr458a, htr567a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hd15b, hd67a, htr159a, htr456a, htr459a, htr567a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd14b, hd78a, htr145a, htr456a, htr567a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd14b, hd67a, htr014a, htr017a, htr178a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd14b, hd79a, htr145a, htr456a, htr567a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd14b, hd67a, htr014a, htr017a, htr179a, htr679a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc156zy, htr016a, htr018a, htr168b, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc356zy, htr138c, htr168b, htr236a, htr238a, htr568a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc367zy, htr378a, htr567a, htr568a, htr678c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd14b, hd67a, htr146a, htr468a, htr567a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      rcases m.htr 5 6 9 (by decide) (by decide) with
        ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
      ·
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc356zy, htr139c, htr169b, htr236a, htr239a, htr569a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc367zy, htr379a, htr567a, htr569a, htr679c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        rcases m.htr 2 3 7 (by decide) (by decide) with
          ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
        ·
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc124xy, hc789zy, htr123a, htr145a, htr237a, htr379a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc156zy, htr168a, htr568b, htr589a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
          ·
            linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a]
        ·
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd13a, hd89b, htr137a, htr237a, htr238a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc134xy, hc389zy, htr137a, htr145a, htr237a, htr239a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc356zy, htr368c, htr389a, htr568a, htr689a]
          ·
            linarith only [hlam, hc156zy, htr168a, htr568b, htr589a, htr689a]
      ·
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr456b, htr469a, htr569a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, htr468b, htr469c, htr489b])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd14b, hd67a, htr148a, htr489a, htr567a, htr568b, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc124xy, hc8910xy, htr012a, htr018a, htr145a, htr1810a, htr458a, htr589a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc156zy, htr168c, htr1810a, htr568a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc156zy, htr168a, htr568b, htr5810a, htr6810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd14b, hd910a, htr145a, htr456a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc134xy, hc8910yz, htr137a, htr145a, htr379a, htr458a, htr5810a, htr7910a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr379a, htr679a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr239a, htr239b, htr239c, _, _⟩
            linarith only [hlam, hc134xy, hc367zy, htr139a, htr145a, htr237a, htr239a, htr456a, htr567a])
          obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
          rcases m.htr 3 9 10 (by decide) (by decide) with
            ⟨htr3910a, htr3910b, htr3910c, _, _⟩ | ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          ·
            linarith only [hlam, hc124xy, hc8910yz, htr123a, htr145a, htr239a, htr3910a, htr458a, htr5810a]
          ·
            linarith only [hlam, hc147yx, hc369zy, htr145a, htr179a, htr3910a, htr456a, htr569a, htr7910a]
        ·
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc124xy, hc679yz, htr123a, htr145a, htr237a, htr379a, htr456a, htr569a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr239a, htr239b, htr239c, _, _⟩
            linarith only [hlam, hc134xy, hc369zy, htr137a, htr145a, htr237a, htr239a, htr456a, htr569a])
          obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
          rcases m.htr 3 9 10 (by decide) (by decide) with
            ⟨htr3910a, htr3910b, htr3910c, _, _⟩ | ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          ·
            linarith only [hlam, hc134xy, hc679yz, htr139a, htr145a, htr3910a, htr456a, htr569a, htr7910a]
          ·
            linarith only [hlam, hd34b, hd69a, htr234a, htr239a, htr3910a, htr6910a]
    ·
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd14b, hd89a, htr145a, htr456a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd14b, hd810a, htr145a, htr456a, htr568a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      rcases m.htr 5 6 9 (by decide) (by decide) with
        ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
      ·
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc356zy, htr139c, htr169b, htr236a, htr239a, htr569a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc367zy, htr379a, htr567a, htr569a, htr679c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc678yz, htr568a, htr569a, htr689c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 2 3 7 (by decide) (by decide) with
          ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
        ·
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc134xy, hc367zy, htr138a, htr145a, htr237a, htr238a, htr456a, htr567a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc124xy, hc678yz, htr123a, htr145a, htr237a, htr378a, htr456a, htr568a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr6810a, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hc147yx, hc368zy, htr145a, htr178a, htr3810a, htr456a, htr568a, htr7810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hc124xy, hc8910zy, htr123a, htr145a, htr238a, htr3810a, htr459a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc156zy, htr169a, htr569b, htr5910a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd910b, htr123a, htr237a, htr379a, htr789c, htr8910a]
          ·
            linarith only [hlam, hd67a, hd89b, htr567a, htr569a, htr6910a, htr8910a]
        ·
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc134xy, hc368zy, htr137a, htr145a, htr237a, htr238a, htr456a, htr568a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hd34b, hd68a, htr234a, htr238a, htr3810a, htr6810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd13a, hd910b, htr137a, htr237a, htr239a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc356zy, htr369c, htr3910a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hc156zy, htr169a, htr569b, htr5910a, htr6910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hc134xy, hc8910zy, htr137a, htr145a, htr378a, htr459a, htr5910a, htr7810a]
          ·
            linarith only [hlam, hc134xy, hc678yz, htr138a, htr145a, htr3810a, htr456a, htr568a, htr7810a]
      ·
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc134xy, hc689yz, htr137a, htr145a, htr378a, htr456a, htr569a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc134xy, hc367zy, htr138a, htr145a, htr237a, htr238a, htr456a, htr567a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          rcases m.htr 3 8 9 (by decide) (by decide) with
            ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
          ·
            linarith only [hlam, hc124xy, hc689yz, htr123a, htr145a, htr238a, htr389a, htr456a, htr569a]
          ·
            linarith only [hlam, hc147yx, hc368zy, htr145a, htr178a, htr389a, htr456a, htr568a, htr789a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc124xy, hc678yz, htr123a, htr145a, htr237a, htr378a, htr456a, htr568a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc134xy, hc368zy, htr137a, htr145a, htr237a, htr238a, htr456a, htr568a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          rcases m.htr 3 8 9 (by decide) (by decide) with
            ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
          ·
            linarith only [hlam, hc134xy, hc678yz, htr138a, htr145a, htr389a, htr456a, htr568a, htr789a]
          ·
            linarith only [hlam, hd34b, hd68a, htr234a, htr238a, htr389a, htr689a]

theorem shard_368 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr139c : m.d 1 9 < m.d 3 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    : False :=
  proof_shard_368 m htr012a htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017c htr123a htr135c htr136c htr137a htr138a htr138c htr139a htr139c htr234a htr235a htr236a

#print axioms shard_368
end Jsp404.NoSatElevenDBMTerminal
