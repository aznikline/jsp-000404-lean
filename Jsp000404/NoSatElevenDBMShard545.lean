import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_545 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc234yx, htr023a, htr027a, htr124a, htr127a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr024c, htr027b, htr047c])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr025c, htr027b, htr057c])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr026c, htr027b, htr067c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr014b, htr047a, htr124b, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc457xy, htr012b, htr027a, htr124a, htr245a, htr247c])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc234yx, htr023a, htr024c, htr045a, htr245a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr015b, htr057a, htr125b, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc567xy, htr012b, htr027a, htr125a, htr256a, htr257c])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc235yx, htr023a, htr025c, htr056a, htr256a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc578yx, htr012b, htr027a, htr125a, htr257c, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hc235yx, htr023a, htr025c, htr058a, htr258a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, htr016b, htr067a, htr126b, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hc678yx, htr012b, htr027a, htr126a, htr267c, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hc236yx, htr023a, htr026c, htr068a, htr268a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc245yz, htr125a, htr127a, htr257c, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc256yz, htr126a, htr127a, htr267c, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd25a, hd67b, htr258a, htr456a, htr458a, htr567a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd24a, hd78b, htr245a, htr456a, htr567a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc247xy, htr124a, htr127b, htr178a, htr278a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc014yx, hc367yz, htr017a, htr045a, htr178a, htr378a, htr456a, htr567a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc014yx, hc678zy, htr013a, htr045a, htr137a, htr378a, htr456a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hc256yz, htr012b, htr028a, htr126a, htr268c, htr568a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hc789xy, htr027a, htr028a, htr278b, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc247xy, htr124a, htr127b, htr179a, htr279a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hc014yx, hc367yz, htr017a, htr045a, htr179a, htr379a, htr456a, htr567a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hc014yx, hc789yz, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc016yx, hc578zy, htr013a, htr068a, htr137a, htr378a, htr589a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd67b, hd78a, htr567a, htr568a, htr689a, htr789a]
    ·
      linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
  ·
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd25a, hd78b, htr256a, htr456a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd24a, hd57b, htr124a, htr127a, htr278a, htr578a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc247xy, htr124a, htr127b, htr178a, htr278a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc015yx, hc357yz, htr017a, htr056a, htr178a, htr378a, htr456a, htr457a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc015yx, hc578zy, htr013a, htr056a, htr137a, htr378a, htr456a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hc245yz, htr012b, htr028a, htr125a, htr258c, htr458a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hc789xy, htr027a, htr028a, htr278b, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc247xy, htr124a, htr127b, htr179a, htr279a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hc015yx, hc357yz, htr017a, htr056a, htr179a, htr379a, htr456a, htr457a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc015yx, hc789yz, htr013a, htr056a, htr137a, htr379a, htr568a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hc015yx, hc678zy, htr013a, htr058a, htr137a, htr378a, htr589a, htr689a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd57b, hd78a, htr457a, htr458a, htr589a, htr789a]
    ·
      linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]

theorem shard_545 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    : False :=
  proof_shard_545 m htr012b htr013a htr014b htr015b htr016b htr017a htr023a htr024c htr025c htr026c htr124a htr124b htr125a htr125b htr126a htr126b htr127a htr127b htr137a

#print axioms shard_545
end Jsp404.NoSatElevenDBMTerminal
