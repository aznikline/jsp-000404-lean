import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_338 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd18a, hd18braw⟩ := m.hrange 1 8 (by decide)
  have hd18b : m.d 1 8 < 4*lam := by
    linarith only [hd18braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
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
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc129xy, hc129yx, hc129yz, hc129zy⟩ := endpoint_caps m 1 2 9 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc158xy, hc158yx, hc158yz, hc158zy⟩ := endpoint_caps m 1 5 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc345yz, htr046c, htr067a, htr356a, htr456c, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc345yz, htr146c, htr167a, htr356a, htr456c, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr012a, htr016a, htr167a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr179a, htr679a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678yx, htr145c, htr156a, htr457a, htr567c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc345yz, htr146c, htr168a, htr356a, htr456c, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679yx, htr145c, htr156a, htr457a, htr567c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc345yz, htr146c, htr169a, htr356a, htr456c, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
        linarith only [hlam, hc6710yx, htr145c, htr156a, htr457a, htr5610a, htr567c])
      obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc345yz, htr146c, htr1610a, htr356a, htr456c, htr5610a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd12a, hd910b, htr012a, htr016a, htr169a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc127xy, hc678zy, htr012a, htr016a, htr168a, htr179a, htr378a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc123xy, hc6910zy, htr012a, htr016a, htr137a, htr1610a, htr379a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc128xy, hc679zy, htr012a, htr016a, htr169a, htr189a, htr7910a, htr8910a]
      ·
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc123xy, hc689zy, htr012a, htr016a, htr137a, htr169a, htr378a, htr789a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc127xy, hc679zy, htr012a, htr016a, htr169a, htr178a, htr378a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc127xy, hc689zy, htr012a, htr016a, htr169a, htr179a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc127xy, hc6910zy, htr012a, htr016a, htr1610a, htr178a, htr789a, htr8910a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc345yz, htr056a, htr057a, htr356a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057c, htr058b, htr078c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc345yz, htr147c, htr178a, htr356a, htr457c, htr567b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc345yz, htr147c, htr179a, htr356a, htr457c, htr567b, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 6 8 (by decide) (by decide) with
        ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc568yz, htr356a, htr358a, htr456b, htr468a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr146c, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc345yz, htr147c, htr178c, htr189a, htr358a, htr457c, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd12a, hd810b, htr012a, htr016a, htr146c, htr468a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr1810a, htr6810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc345yz, htr147c, htr178c, htr1810a, htr358a, htr457c, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc123xy, hc678zy, htr012a, htr013c, htr016a, htr035c, htr058a, htr146c, htr468a, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hc123xy, hc689zy, htr012a, htr013c, htr016a, htr035c, htr057a, htr169a, htr578a, htr789a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc123xy, hc678zy, htr012a, htr013c, htr016a, htr035c, htr058a, htr146c, htr468a, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc123xy, hc8910yz, htr012a, htr013c, htr019a, htr035c, htr057a, htr1910a, htr578a, htr7810a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd67b, hd89a, htr167a, htr169a, htr6910a, htr8910a]
        ·
          linarith only [hlam, hd45b, hd910a, htr457a, htr578a, htr789a, htr8910a]
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc345yz, htr056b, htr068a, htr356a, htr456c, htr468a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        rcases m.htr 5 6 9 (by decide) (by decide) with
          ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
        ·
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, hc678yx, htr067a, htr069a, htr568a, htr569a])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr068c, htr069b, htr089c])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc678yx, htr167a, htr169a, htr568a, htr569a])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, htr356c, htr369a, htr569a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr156a, htr189a, htr568a, htr6810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
            linarith only [hlam, hc678yx, htr148c, htr1810a, htr467a, htr468c, htr6810a])
          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr012a, htr016a, htr169a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc689xy, htr368a, htr369b, htr3910a, htr6910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            linarith only [hlam, hc123xy, hc679zy, htr012a, htr016a, htr139a, htr169a, htr3910a, htr7910a]
          ·
            linarith only [hlam, hc123xy, hc8910zy, htr012a, htr013c, htr018a, htr035c, htr057a, htr1810a, htr579a, htr7910a]
        ·
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr056b, htr069a, htr569a])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc125xy, htr012a, htr016a, htr156a, htr169a, htr569a])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          rcases m.htr 5 6 10 (by decide) (by decide) with
            ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
          ·
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, hc678yx, htr0610a, htr067a, htr5610a, htr568a])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0610b, htr068c, htr0810c])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
              linarith only [hlam, htr0610b, htr069c, htr0910c])
            obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
              linarith only [hlam, hc129xy, htr012a, htr019b, htr0910a, htr1910a])
            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc678yx, htr148c, htr189a, htr467a, htr468c, htr689a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
            ·
              linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
          ·
            rcases m.htr 4 8 9 (by decide) (by decide) with
              ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
            ·
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr148c, htr156a, htr489a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc678yx, htr148c, htr1810a, htr467a, htr468c, htr6810a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr148c, htr489a, htr8910a]
              ·
                linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc678yx, htr467a, htr468c, htr489a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc678yx, htr148c, htr1810a, htr467a, htr468c, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd45b, hd89a, htr456a, htr569a, htr6910a, htr8910a]
              ·
                linarith only [hlam, hd67b, hd910a, htr467a, htr468a, htr689a, htr8910a]
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567c])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr056b, htr067a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr015c, htr056a, htr157a, htr567c])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc125xy, htr012a, htr016a, htr156a, htr167a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, htr145c, htr156a, htr457a, htr567c])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    rcases m.htr 3 5 7 (by decide) (by decide) with
      ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
    ·
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc678xy, htr056a, htr058a, htr567a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc345yz, htr046c, htr068a, htr356a, htr456c, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr067c, htr068b, htr078c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc345yz, htr146c, htr168a, htr356a, htr456c, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr356c, htr368a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc125xy, hc789yx, htr012a, htr017a, htr156a, htr178a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr679a])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc678xy, htr167c, htr168a, htr179a, htr679a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc579yz, htr057b, htr079a, htr357a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc125xy, hc7810yx, htr012a, htr017a, htr156a, htr178a, htr567a, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
          linarith only [hlam, hc678xy, htr167c, htr168a, htr1710a, htr6710a])
        obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hc678xy, htr058b, htr089a, htr567a, htr568b, htr689a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr058c, htr059b, htr089c])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr015c, htr059a, htr159a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc678xy, htr367a, htr368b, htr389a, htr689a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr012a, htr017a, htr179a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hd12a, hd79b, htr012a, htr019a, htr1910a, htr7910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc135zy, htr159c, htr1910a, htr359a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc789zy, htr012a, htr013c, htr017a, htr035c, htr059a, htr179a, htr5910a, htr8910a]
        ·
          linarith only [hlam, hc123xy, hc7910zy, htr012a, htr017a, htr138a, htr1710a, htr389a, htr8910a]
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015c, htr056a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 3 5 8 (by decide) (by decide) with
          ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
        ·
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, hc345yz, htr046c, htr069a, htr356a, htr456c, htr569a])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr067c, htr069b, htr079c])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, htr068c, htr069b, htr089c])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc345yz, htr146c, htr169a, htr356a, htr456c, htr569a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc127xy, htr012a, htr017b, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc125xy, hc789xy, htr012a, htr017a, htr156a, htr179a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc679xy, htr167c, htr169a, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
            ·
              linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
          ·
            rcases m.htr 3 5 9 (by decide) (by decide) with
              ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
            ·
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc345yz, htr046c, htr0610a, htr356a, htr456c, htr5610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0610b, htr067c, htr0710c])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610b, htr068c, htr0810c])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                  linarith only [hlam, hc345yz, htr146c, htr1610a, htr356a, htr456c, htr5610a])
                obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
                have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                  linarith only [hlam, hc127xy, htr012a, htr017b, htr0710a, htr1710a])
                obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc125xy, hc7810xy, htr012a, htr017a, htr156a, htr1710a, htr567a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc6710xy, htr1610a, htr167c, htr178a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd810b, htr012a, htr017a, htr178a, htr7810a]
                ·
                  linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr1810a, htr7810a]
              ·
                rcases m.htr 3 5 10 (by decide) (by decide) with
                  ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                ·
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    rcases m.htr 4 7 8 (by decide) (by decide) with
                      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                    ·
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, htr137b, htr147c, htr378a, htr478a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr147c, htr478a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc135zy, htr158c, htr189a, htr358a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc125xy, hc678yz, htr012a, htr017a, htr147c, htr156a, htr478a, htr568c, htr589a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hc125xy, hc789zy, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc135zy, htr157c, htr179a, htr357a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc345yz, htr357b, htr379a, htr456a, htr567c, htr579a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                        linarith only [hlam, hc128xy, hc789yx, htr012a, htr017a, htr147c, htr1810a, htr378b, htr379a, htr3810a, htr478a])
                      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                        linarith only [hlam, hc123xy, hc678yz, htr012a, htr017a, htr138a, htr147c, htr3810a, htr478a, htr6810a])
                      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                        linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
                      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                        linarith only [hlam, hc789yx, htr147c, htr179c, htr1910a, htr478a, htr7910a])
                      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd78b, hd89a, htr147c, htr179a, htr478a, htr7910a, htr8910a]
                      ·
                        linarith only [hlam, hd45b, hd910a, htr456a, htr568a, htr689a, htr8910a]
                    ·
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc345yz, htr057b, htr078a, htr357a, htr457c, htr478a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc345yz, htr357b, htr378a, htr456a, htr567c, htr578a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hd45b, hd79a, htr456a, htr567c, htr578a, htr678a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      rcases m.htr 5 7 9 (by decide) (by decide) with
                        ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc067zy, htr079a, htr578a, htr579a, htr678a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, htr078c, htr079b, htr089c])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc167zy, htr179a, htr578a, htr579a, htr678a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, htr357c, htr379a, htr579a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr156a, htr189a, htr567c, htr578a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hc467zy, htr148c, htr1810a, htr478c, htr678a, htr7810a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                          linarith only [hlam, hc123xy, hc679yz, htr012a, htr017a, htr139a, htr179a, htr3910a, htr6910a])
                        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                        ·
                          linarith only [hlam, hd67a, hd89b, htr378a, htr379b, htr3910a, htr678a, htr8910a]
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057b, htr079a, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc125xy, htr012a, htr017a, htr156a, htr179a, htr567c, htr579a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc567zy, htr378a, htr379a, htr579a, htr678a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        rcases m.htr 5 7 10 (by decide) (by decide) with
                          ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                        ·
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, hc067zy, htr0710a, htr5710a, htr578a, htr678a])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                            linarith only [hlam, htr0710b, htr078c, htr0810c])
                          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                          have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                            linarith only [hlam, htr0710b, htr079c, htr0910c])
                          obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                            linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
                          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                            linarith only [hlam, hc129xy, htr012a, htr019b, htr0910a, htr1910a])
                          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr567c, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc467zy, htr148c, htr189a, htr478c, htr678a, htr789a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                          ·
                            linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
                        ·
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                              linarith only [hlam, hc467zy, htr148c, htr189a, htr478c, htr678a, htr789a])
                            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr156a, htr189a, htr567c, htr578a, htr7810a])
                            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                              linarith only [hlam, hc467zy, htr148c, htr1810a, htr478c, htr678a, htr7810a])
                            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                            have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                              linarith only [hlam, hc123xy, hc689yz, htr012a, htr018a, htr139a, htr189a, htr3910a, htr6910a])
                            obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                              linarith only [hlam, hc167zy, htr179c, htr1910a, htr379b, htr3910a, htr679a])
                            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                            ·
                              linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
                          ·
                            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr567c, htr578a, htr789a])
                            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                            have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                              linarith only [hlam, hc467zy, htr148c, htr1810a, htr378b, htr3810a, htr478c, htr678a])
                            obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                              linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
                            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                              linarith only [hlam, hd13b, hd89a, htr138a, htr3810a, htr6810a, htr689a])
                            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
                            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                              linarith only [hlam, hc167zy, htr179c, htr1910a, htr679a, htr7910a])
                            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd45b, hd89a, htr456a, htr567c, htr579a, htr7910a, htr8910a]
                            ·
                              linarith only [hlam, hd45b, hd910a, htr456a, htr567c, htr578a, htr789a, htr8910a]
                  ·
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hc125xy, hc789xy, htr012a, htr017a, htr156a, htr179a, htr567a, htr678a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                      linarith only [hlam, hc125xy, hc7810xy, htr012a, htr017a, htr156a, htr1710a, htr567a, htr678a])
                    obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hc135zy, htr157c, htr179a, htr357a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      linarith only [hlam, hc135zy, htr157c, htr1710a, htr357a, htr5710a])
                    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr579a, htr678a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc125xy, hc789yz, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hc135zy, htr158c, htr189a, htr358a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr5710a, htr6710a, htr678a])
                    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc125xy, hc7910yz, htr012a, htr019a, htr156a, htr1910a, htr567a, htr6710a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd45b, hd910a, htr456a, htr567a, htr679a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc178zy, htr189c, htr1910a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hd45b, hd79a, htr456a, htr568c, htr589a, htr7910a, htr8910a]
                ·
                  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                    linarith only [hlam, htr3510c, htr357b, htr3710b])
                  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                  have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                    linarith only [hlam, htr3510c, htr358b, htr3810b])
                  obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, htr357c, htr3710a, htr5710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc7810yx, htr3510a, htr357a, htr5710b, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                    linarith only [hlam, htr358c, htr3810a, htr5810a])
                  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd45b, hd67a, htr3510a, htr356a, htr456a, htr5710b, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd45b, hd710a, htr456a, htr567c, htr578a, htr6710a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  rcases m.htr 7 8 10 (by decide) (by decide) with
                    ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  ·
                    linarith only [hlam, hd45b, hd78a, htr3510a, htr356a, htr456a, htr5810b, htr7810a]
                  ·
                    linarith only [hlam, hd45b, hd810a, htr456a, htr567a, htr678a, htr7810a]
            ·
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, htr357b, htr359c, htr379b])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, htr358b, htr359c, htr389b])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, htr357c, htr379a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc789yx, htr357a, htr359a, htr578a, htr579b])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, htr358c, htr389a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr356a, htr359a, htr456a, htr579b, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd45b, hd79a, htr456a, htr567c, htr578a, htr678a, htr679a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd45b, hd78a, htr356a, htr359a, htr456a, htr589b, htr789a]
              ·
                linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, htr357b, htr358c, htr378b])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, htr357c, htr378a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc789xy, htr357a, htr358a, htr578b, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc7810xy, htr357a, htr358a, htr5710a, htr578b])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd45b, hd89a, htr356a, htr358a, htr456a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr356a, htr358a, htr456a, htr578b, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr579a, htr678a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc125xy, hc789yz, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, hc158zy, htr189a, htr358a, htr359a, htr589c])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd45b, hd910a, htr356a, htr359a, htr456a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr5710a, htr6710a, htr678a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
            linarith only [hlam, hc125xy, hc7910yz, htr012a, htr019a, htr156a, htr1910a, htr567a, htr6710a])
          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc158zy, htr189c, htr1910a, htr589a, htr8910a]
          ·
            linarith only [hlam, hc158zy, htr189a, htr589b, htr5910a, htr8910a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc578xy, htr056a, htr058a, htr356a, htr357a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc579xy, htr056a, htr059a, htr356a, htr357a])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678xy, htr356a, htr357a, htr567b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679xy, htr356a, htr357a, htr567b, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr356a, htr357a, htr456a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd45b, hd79a, htr356a, htr357a, htr456a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc125xy, hc578yz, htr012a, htr017a, htr147c, htr156a, htr356a, htr358a, htr478a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr147c, htr478a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd57a, hd78b, htr357a, htr358a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc123xy, hc678yz, htr012a, htr013c, htr017a, htr035c, htr058a, htr147c, htr478a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc125xy, hc789zy, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc157zy, htr179a, htr357a, htr359a, htr579c])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd18b, hd57a, htr1810a, htr357a, htr358a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd45b, hd910a, htr356a, htr359a, htr456a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc123xy, hc678yz, htr012a, htr013c, htr017a, htr035c, htr058a, htr147c, htr478a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc157zy, htr179c, htr1910a, htr579a, htr7910a]
        ·
          linarith only [hlam, hc157zy, htr179a, htr579b, htr5910a, htr7910a]
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc457zy, htr357a, htr358a, htr478a, htr578c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45b, hd89a, htr356a, htr358a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd45b, hd810a, htr356a, htr358a, htr456a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc457zy, htr148c, htr189a, htr478c, htr578a, htr789a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc125xy, hc589yz, htr012a, htr018a, htr156a, htr189a, htr356a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc457zy, htr478a, htr578b, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc457zy, htr148c, htr1810a, htr478c, htr578a, htr7810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc123xy, hc689yz, htr012a, htr013c, htr018a, htr035c, htr059a, htr189a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
        ·
          linarith only [hlam, hd57a, hd89b, htr357a, htr359a, htr5910a, htr8910a]

theorem shard_338 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_338 m htr012a htr013c htr015c htr016a htr017a htr017b htr018a htr018b htr019a htr019b htr035c htr046c htr056a htr056b htr137a htr137b htr138a htr139a htr145c htr146c htr147c htr148c htr156a htr356a htr356b htr356c htr456a htr456b htr456c

#print axioms shard_338
end Jsp404.NoSatElevenDBMTerminal
