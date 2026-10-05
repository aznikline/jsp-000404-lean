import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_302 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
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
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr013c, htr017b, htr037c])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr014c, htr017b, htr047c])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr015c, htr017b, htr057c])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr016c, htr017b, htr067c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, htr013b, htr037a, htr137a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc347xy, htr013a, htr017a, htr134a, htr137c])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, htr014b, htr047a, htr147a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc457xy, htr014a, htr017a, htr145a, htr147c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc467xy, htr014a, htr017a, htr146a, htr147c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr015b, htr057a, htr157a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc567xy, htr015a, htr017a, htr156a, htr157c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
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
  have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
    linarith only [hlam, hc6710yx, htr016a, htr017a, htr1610a, htr167c])
  obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc134yz, htr014a, htr017a, htr147c, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc145yz, htr015a, htr017a, htr157c, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hc146yz, htr016a, htr017a, htr167c, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc156yz, htr016a, htr017a, htr167c, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 3 4 5 (by decide) (by decide) with
    ⟨htr345a, htr345b, htr345c, _, _⟩ | ⟨htr345a, htr345b, htr345c, _, _⟩
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd14a, hd57b, htr146a, htr345a, htr346a, htr457a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr134a, htr345a, htr456a, htr567a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc145yz, htr156b, htr168a, htr456a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd15a, hd67b, htr156a, htr467a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc145yz, htr156b, htr169a, htr456a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd15a, hd67b, htr156a, htr467a, htr469a, htr569a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
      linarith only [hlam, hc145yz, htr156b, htr1610a, htr456a, htr5610a])
    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hd15a, hd67b, htr156a, htr4610a, htr467a, htr5610a])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr134a, htr345a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd13a, hd57b, htr013a, htr017a, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd13a, hd79b, htr134a, htr345a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd13a, hd57b, htr013a, htr017a, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
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
      linarith only [hlam, hd13a, hd89b, htr134a, htr346a, htr468a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd13a, hd910b, htr134a, htr346a, htr469a, htr6910a])
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
        linarith only [hlam, hc137xy, hc678zy, htr134a, htr179a, htr278a, htr279a, htr346a, htr468a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc123yx, hc6910zy, htr127a, htr134a, htr279a, htr346a, htr4610a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc123yx, hc689zy, htr127a, htr134a, htr278a, htr346a, htr469a, htr789a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc137xy, hc679zy, htr134a, htr178a, htr278a, htr279a, htr346a, htr469a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc267yz, htr279a, htr679c, htr6910a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc137xy, hc689zy, htr134a, htr179a, htr346a, htr469a, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc137xy, hc6910zy, htr134a, htr178a, htr346a, htr4610a, htr789a, htr8910a]
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd14a, hd67b, htr145a, htr345a, htr346a, htr467a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr156a, htr345a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr168a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr169a, htr346a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr1610a, htr346a, htr4610a])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd14a, hd78b, htr145a, htr345a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd13a, hd47b, htr013a, htr017a, htr178a, htr478a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd14a, hd79b, htr145a, htr345a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd13a, hd47b, htr013a, htr017a, htr179a, htr479a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd14a, hd67b, htr146a, htr468a, htr567a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hd14a, hd67b, htr146a, htr469a, htr567a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
      linarith only [hlam, hd14a, hd67b, htr146a, htr4610a, htr5610a, htr567a])
    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, htr467c, htr478a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, htr467c, htr479a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd14a, hd89b, htr145a, htr456a, htr568a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd14a, hd910b, htr145a, htr456a, htr569a, htr6910a])
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
        linarith only [hlam, hc147xy, hc678zy, htr145a, htr179a, htr278a, htr279a, htr456a, htr568a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc124yx, hc6910zy, htr127a, htr145a, htr279a, htr456a, htr5610a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc124yx, hc689zy, htr127a, htr145a, htr278a, htr456a, htr569a, htr789a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc147xy, hc679zy, htr145a, htr178a, htr278a, htr279a, htr456a, htr569a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc267yz, htr279a, htr679c, htr6910a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc147xy, hc689zy, htr145a, htr179a, htr456a, htr569a, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc147xy, hc6910zy, htr145a, htr178a, htr456a, htr5610a, htr789a, htr8910a]

theorem shard_302 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    : False :=
  proof_shard_302 m htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr127a

#print axioms shard_302
end Jsp404.NoSatElevenDBMTerminal
