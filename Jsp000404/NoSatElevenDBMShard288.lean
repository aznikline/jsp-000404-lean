import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_288 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
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
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc139xy, hc139yx, hc139yz, hc139zy⟩ := endpoint_caps m 1 3 9 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc158xy, hc158yx, hc158yz, hc158zy⟩ := endpoint_caps m 1 5 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
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
      linarith only [hlam, hc245yz, htr046c, htr067a, htr256a, htr456c, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc245yz, htr146c, htr167a, htr256a, htr456c, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr013a, htr016a, htr167a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr178a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc137xy, htr013a, htr017b, htr078a, htr178a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd13a, hd79b, htr013a, htr016a, htr167a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr179a, htr679a])
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
        linarith only [hlam, hc245yz, htr146c, htr168a, htr256a, htr456c, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679yx, htr145c, htr156a, htr457a, htr567c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc245yz, htr146c, htr169a, htr256a, htr456c, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
        linarith only [hlam, hc6710yx, htr145c, htr156a, htr457a, htr5610a, htr567c])
      obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc245yz, htr146c, htr1610a, htr256a, htr456c, htr5610a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr013a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd13a, hd68b, htr013a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd13a, hd910b, htr013a, htr016a, htr169a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc267yz, htr278a, htr678c, htr689a, htr789a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc137xy, hc678zy, htr013a, htr016a, htr168a, htr179a, htr278a, htr279a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc123yx, hc6910zy, htr013a, htr016a, htr127a, htr1610a, htr279a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc138xy, hc679zy, htr013a, htr016a, htr169a, htr189a, htr7910a, htr8910a]
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc123yx, hc689zy, htr013a, htr016a, htr127a, htr169a, htr278a, htr789a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc137xy, hc679zy, htr013a, htr016a, htr169a, htr178a, htr278a, htr279a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc267yz, htr279a, htr679c, htr6910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc137xy, hc689zy, htr013a, htr016a, htr169a, htr179a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc137xy, hc6910zy, htr013a, htr016a, htr1610a, htr178a, htr789a, htr8910a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc245yz, htr056a, htr057a, htr256a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057c, htr058b, htr078c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc245yz, htr147c, htr178a, htr256a, htr457c, htr567b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc245yz, htr147c, htr179a, htr256a, htr457c, htr567b, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 6 8 (by decide) (by decide) with
        ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc568yz, htr256a, htr258a, htr456b, htr468a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr013a, htr016a, htr146c, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hd13a, hd68b, htr013a, htr018a, htr189a, htr689a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc245yz, htr147c, htr178c, htr189a, htr258a, htr457c, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd13a, hd810b, htr013a, htr016a, htr146c, htr468a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hd13a, hd68b, htr013a, htr018a, htr1810a, htr6810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc245yz, htr147c, htr178c, htr1810a, htr258a, htr457c, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc123yx, hc678zy, htr012c, htr013a, htr016a, htr025c, htr058a, htr146c, htr468a, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hc123yx, hc689zy, htr012c, htr013a, htr016a, htr025c, htr057a, htr169a, htr578a, htr789a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc123yx, hc678zy, htr012c, htr013a, htr016a, htr025c, htr058a, htr146c, htr468a, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc123yx, hc8910yz, htr012c, htr013a, htr019a, htr025c, htr057a, htr1910a, htr578a, htr7810a])
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
          linarith only [hlam, hc245yz, htr056b, htr068a, htr256a, htr456c, htr468a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
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
            linarith only [hlam, hc138xy, htr013a, htr018b, htr089a, htr189a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, htr256c, htr269a, htr569a])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hc135xy, hc8910yx, htr013a, htr018a, htr156a, htr189a, htr568a, htr6810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
            linarith only [hlam, hc678yx, htr148c, htr1810a, htr467a, htr468c, htr6810a])
          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd13a, hd910b, htr013a, htr016a, htr169a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
            linarith only [hlam, hc689xy, htr268a, htr269b, htr2910a, htr6910a])
          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            linarith only [hlam, hc123yx, hc679zy, htr013a, htr016a, htr129a, htr169a, htr2910a, htr7910a]
          ·
            linarith only [hlam, hc123yx, hc8910zy, htr012c, htr013a, htr018a, htr025c, htr057a, htr1810a, htr579a, htr7910a]
        ·
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr056b, htr069a, htr569a])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc135xy, htr013a, htr016a, htr156a, htr169a, htr569a])
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
              linarith only [hlam, hc138xy, htr013a, htr018b, htr0810a, htr1810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
              linarith only [hlam, hc139xy, htr013a, htr019b, htr0910a, htr1910a])
            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc135xy, hc8910xy, htr013a, htr018a, htr156a, htr1810a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc678yx, htr148c, htr189a, htr467a, htr468c, htr689a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd910b, htr013a, htr018a, htr189a, htr8910a]
            ·
              linarith only [hlam, hd13a, hd89b, htr013a, htr019a, htr1910a, htr8910a]
          ·
            rcases m.htr 4 8 9 (by decide) (by decide) with
              ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
            ·
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc135xy, hc8910yx, htr013a, htr018a, htr148c, htr156a, htr489a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc678yx, htr148c, htr1810a, htr467a, htr468c, htr6810a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc135xy, hc8910zy, htr013a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd13a, hd910b, htr013a, htr018a, htr148c, htr489a, htr8910a]
              ·
                linarith only [hlam, hd13a, hd89b, htr013a, htr019a, htr1910a, htr8910a]
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc678yx, htr467a, htr468c, htr489a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc135xy, hc8910xy, htr013a, htr018a, htr156a, htr1810a, htr568a, htr689a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc678yx, htr148c, htr1810a, htr467a, htr468c, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc135xy, hc8910yz, htr013a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
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
      linarith only [hlam, hc135xy, htr013a, htr016a, htr156a, htr167a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, htr145c, htr156a, htr457a, htr567c])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    rcases m.htr 2 5 7 (by decide) (by decide) with
      ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
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
          linarith only [hlam, hc245yz, htr046c, htr068a, htr256a, htr456c, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr067c, htr068b, htr078c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc245yz, htr146c, htr168a, htr256a, htr456c, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc137xy, htr013a, htr017b, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr256c, htr268a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc135xy, hc789yx, htr013a, htr017a, htr156a, htr178a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr679a])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc678xy, htr167c, htr168a, htr179a, htr679a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc579yz, htr057b, htr079a, htr257a, htr259a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc135xy, hc7810yx, htr013a, htr017a, htr156a, htr178a, htr567a, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
          linarith only [hlam, hc678xy, htr167c, htr168a, htr1710a, htr6710a])
        obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr013a, htr016a, htr168a, htr689a])
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
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc678xy, htr267a, htr268b, htr289a, htr689a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd13a, hd910b, htr013a, htr017a, htr179a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hd13a, hd79b, htr013a, htr019a, htr1910a, htr7910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc125zy, htr159c, htr1910a, htr259a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc123yx, hc789zy, htr012c, htr013a, htr017a, htr025c, htr059a, htr179a, htr5910a, htr8910a]
        ·
          linarith only [hlam, hc123yx, hc7910zy, htr013a, htr017a, htr128a, htr1710a, htr289a, htr8910a]
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015c, htr056a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 2 5 8 (by decide) (by decide) with
          ⟨htr258a, htr258b, htr258c, _, _⟩ | ⟨htr258a, htr258b, htr258c, _, _⟩
        ·
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, hc245yz, htr046c, htr069a, htr256a, htr456c, htr569a])
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
              linarith only [hlam, hc245yz, htr146c, htr169a, htr256a, htr456c, htr569a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc137xy, htr013a, htr017b, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc138xy, htr013a, htr018b, htr089a, htr189a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc135xy, hc789xy, htr013a, htr017a, htr156a, htr179a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc679xy, htr167c, htr169a, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd89b, htr013a, htr017a, htr178a, htr789a]
            ·
              linarith only [hlam, hd13a, hd78b, htr013a, htr018a, htr189a, htr789a]
          ·
            rcases m.htr 2 5 9 (by decide) (by decide) with
              ⟨htr259a, htr259b, htr259c, _, _⟩ | ⟨htr259a, htr259b, htr259c, _, _⟩
            ·
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc245yz, htr046c, htr0610a, htr256a, htr456c, htr5610a])
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
                  linarith only [hlam, hc245yz, htr146c, htr1610a, htr256a, htr456c, htr5610a])
                obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
                have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                  linarith only [hlam, hc137xy, htr013a, htr017b, htr0710a, htr1710a])
                obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc138xy, htr013a, htr018b, htr0810a, htr1810a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc135xy, hc7810xy, htr013a, htr017a, htr156a, htr1710a, htr567a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc6710xy, htr1610a, htr167c, htr178a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd810b, htr013a, htr017a, htr178a, htr7810a]
                ·
                  linarith only [hlam, hd13a, hd78b, htr013a, htr018a, htr1810a, htr7810a]
              ·
                rcases m.htr 2 5 10 (by decide) (by decide) with
                  ⟨htr2510a, htr2510b, htr2510c, _, _⟩ | ⟨htr2510a, htr2510b, htr2510c, _, _⟩
                ·
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    rcases m.htr 4 7 8 (by decide) (by decide) with
                      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                    ·
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, htr127b, htr147c, htr278a, htr478a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hd13a, hd89b, htr013a, htr017a, htr147c, htr478a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hd13a, hd78b, htr013a, htr018a, htr189a, htr789a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc125zy, htr158c, htr189a, htr258a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc135xy, hc678yz, htr013a, htr017a, htr147c, htr156a, htr478a, htr568c, htr589a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hc135xy, hc789zy, htr013a, htr017a, htr156a, htr179a, htr568a, htr689a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hc135xy, hc8910xy, htr013a, htr018a, htr156a, htr1810a, htr568a, htr689a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc125zy, htr157c, htr179a, htr257a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc245yz, htr257b, htr279a, htr456a, htr567c, htr579a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hc138xy, hc789yx, htr013a, htr017a, htr147c, htr1810a, htr278b, htr279a, htr2810a, htr478a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                        linarith only [hlam, hc123yx, hc678yz, htr013a, htr017a, htr128a, htr147c, htr2810a, htr478a, htr6810a])
                      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                        linarith only [hlam, hc135xy, hc8910yz, htr013a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
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
                        linarith only [hlam, hc245yz, htr057b, htr078a, htr257a, htr457c, htr478a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, hc245yz, htr257b, htr278a, htr456a, htr567c, htr578a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
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
                          linarith only [hlam, hc138xy, htr013a, htr018b, htr089a, htr189a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, htr257c, htr279a, htr579a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc135xy, hc8910yx, htr013a, htr018a, htr156a, htr189a, htr567c, htr578a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hc467zy, htr148c, htr1810a, htr478c, htr678a, htr7810a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc135xy, hc8910zy, htr013a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                          linarith only [hlam, hc123yx, hc679yz, htr013a, htr017a, htr129a, htr179a, htr2910a, htr6910a])
                        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd13a, hd910b, htr013a, htr018a, htr189a, htr8910a]
                        ·
                          linarith only [hlam, hd67a, hd89b, htr278a, htr279b, htr2910a, htr678a, htr8910a]
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057b, htr079a, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc135xy, htr013a, htr017a, htr156a, htr179a, htr567c, htr579a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc567zy, htr278a, htr279a, htr579a, htr678a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
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
                            linarith only [hlam, hc138xy, htr013a, htr018b, htr0810a, htr1810a])
                          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                            linarith only [hlam, hc139xy, htr013a, htr019b, htr0910a, htr1910a])
                          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hc135xy, hc8910xy, htr013a, htr018a, htr156a, htr1810a, htr567c, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc467zy, htr148c, htr189a, htr478c, htr678a, htr789a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd13a, hd910b, htr013a, htr018a, htr189a, htr8910a]
                          ·
                            linarith only [hlam, hd13a, hd89b, htr013a, htr019a, htr1910a, htr8910a]
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
                              linarith only [hlam, hc135xy, hc8910yx, htr013a, htr018a, htr156a, htr189a, htr567c, htr578a, htr7810a])
                            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                              linarith only [hlam, hc467zy, htr148c, htr1810a, htr478c, htr678a, htr7810a])
                            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                              linarith only [hlam, hc135xy, hc8910zy, htr013a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                            have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                              linarith only [hlam, hc123yx, hc689yz, htr013a, htr018a, htr129a, htr189a, htr2910a, htr6910a])
                            obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                              linarith only [hlam, hc167zy, htr179c, htr1910a, htr279b, htr2910a, htr679a])
                            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd13a, hd910b, htr013a, htr018a, htr189a, htr8910a]
                            ·
                              linarith only [hlam, hd13a, hd89b, htr013a, htr019a, htr1910a, htr8910a]
                          ·
                            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                              linarith only [hlam, hc135xy, hc8910xy, htr013a, htr018a, htr156a, htr1810a, htr567c, htr578a, htr789a])
                            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                              linarith only [hlam, hc467zy, htr148c, htr1810a, htr278b, htr2810a, htr478c, htr678a])
                            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                              linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
                            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                              linarith only [hlam, hd12b, hd89a, htr128a, htr2810a, htr6810a, htr689a])
                            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                              linarith only [hlam, hc135xy, hc8910yz, htr013a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
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
                      linarith only [hlam, hc135xy, hc789xy, htr013a, htr017a, htr156a, htr179a, htr567a, htr678a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                      linarith only [hlam, hc135xy, hc7810xy, htr013a, htr017a, htr156a, htr1710a, htr567a, htr678a])
                    obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hc125zy, htr157c, htr179a, htr257a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      linarith only [hlam, hc125zy, htr157c, htr1710a, htr257a, htr5710a])
                    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr579a, htr678a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc135xy, hc789yz, htr013a, htr018a, htr156a, htr189a, htr567a, htr679a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hc125zy, htr158c, htr189a, htr258a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr5710a, htr6710a, htr678a])
                    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc135xy, hc7910yz, htr013a, htr019a, htr156a, htr1910a, htr567a, htr6710a])
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
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, htr2510c, htr257b, htr2710b])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                    linarith only [hlam, htr2510c, htr258b, htr2810b])
                  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, htr257c, htr2710a, htr5710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc7810yx, htr2510a, htr257a, htr5710b, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                    linarith only [hlam, htr258c, htr2810a, htr5810a])
                  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd45b, hd67a, htr2510a, htr256a, htr456a, htr5710b, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd45b, hd710a, htr456a, htr567c, htr578a, htr6710a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  rcases m.htr 7 8 10 (by decide) (by decide) with
                    ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  ·
                    linarith only [hlam, hd45b, hd78a, htr2510a, htr256a, htr456a, htr5810b, htr7810a]
                  ·
                    linarith only [hlam, hd45b, hd810a, htr456a, htr567a, htr678a, htr7810a]
            ·
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, htr257b, htr259c, htr279b])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, htr258b, htr259c, htr289b])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, htr257c, htr279a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc789yx, htr257a, htr259a, htr578a, htr579b])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, htr258c, htr289a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr256a, htr259a, htr456a, htr579b, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd45b, hd79a, htr456a, htr567c, htr578a, htr678a, htr679a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd45b, hd78a, htr256a, htr259a, htr456a, htr589b, htr789a]
              ·
                linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a]
        ·
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, htr257b, htr258c, htr278b])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, htr257c, htr278a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc789xy, htr257a, htr258a, htr578b, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc7810xy, htr257a, htr258a, htr5710a, htr578b])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd45b, hd89a, htr256a, htr258a, htr456a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr256a, htr258a, htr456a, htr578b, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr579a, htr678a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc135xy, hc789yz, htr013a, htr018a, htr156a, htr189a, htr567a, htr679a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr259a, htr259b, htr259c, _, _⟩
            linarith only [hlam, hc158zy, htr189a, htr258a, htr259a, htr589c])
          obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd45b, hd910a, htr256a, htr259a, htr456a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd45b, hd78a, htr456a, htr567c, htr5710a, htr6710a, htr678a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
            linarith only [hlam, hc135xy, hc7910yz, htr013a, htr019a, htr156a, htr1910a, htr567a, htr6710a])
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
        linarith only [hlam, hc578xy, htr056a, htr058a, htr256a, htr257a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc579xy, htr056a, htr059a, htr256a, htr257a])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678xy, htr256a, htr257a, htr567b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679xy, htr256a, htr257a, htr567b, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr256a, htr257a, htr456a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd45b, hd79a, htr256a, htr257a, htr456a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135xy, hc578yz, htr013a, htr017a, htr147c, htr156a, htr256a, htr258a, htr478a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr013a, htr017a, htr147c, htr478a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd57a, hd78b, htr257a, htr258a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc123yx, hc678yz, htr012c, htr013a, htr017a, htr025c, htr058a, htr147c, htr478a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc135xy, hc789zy, htr013a, htr017a, htr156a, htr179a, htr568a, htr689a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc135xy, hc8910xy, htr013a, htr018a, htr156a, htr1810a, htr568a, htr689a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc157zy, htr179a, htr257a, htr259a, htr579c])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd18b, hd57a, htr1810a, htr257a, htr258a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd45b, hd910a, htr256a, htr259a, htr456a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc123yx, hc678yz, htr012c, htr013a, htr017a, htr025c, htr058a, htr147c, htr478a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc135xy, hc8910yz, htr013a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc157zy, htr179c, htr1910a, htr579a, htr7910a]
        ·
          linarith only [hlam, hc157zy, htr179a, htr579b, htr5910a, htr7910a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc457zy, htr257a, htr258a, htr478a, htr578c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45b, hd89a, htr256a, htr258a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd45b, hd810a, htr256a, htr258a, htr456a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc457zy, htr148c, htr189a, htr478c, htr578a, htr789a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc135xy, hc589yz, htr013a, htr018a, htr156a, htr189a, htr256a, htr259a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
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
          linarith only [hlam, hc135xy, hc8910zy, htr013a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc123yx, hc689yz, htr012c, htr013a, htr018a, htr025c, htr059a, htr189a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd13a, hd910b, htr013a, htr018a, htr189a, htr8910a]
        ·
          linarith only [hlam, hd57a, hd89b, htr257a, htr259a, htr5910a, htr8910a]

theorem shard_288 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_288 m htr012c htr013a htr015c htr016a htr017a htr017b htr018a htr018b htr019a htr019b htr025c htr046c htr056a htr056b htr127a htr127b htr128a htr129a htr145c htr146c htr147c htr148c htr156a htr256a htr256b htr256c htr456a htr456b htr456c

#print axioms shard_288
end Jsp404.NoSatElevenDBMTerminal
