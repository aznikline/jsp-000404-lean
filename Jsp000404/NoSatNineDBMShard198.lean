import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_198 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < (7/2 : ℝ)*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd18a, hd18braw⟩ := m.hrange 1 8 (by decide)
  have hd18b : m.d 1 8 < (7/2 : ℝ)*lam := by
    linarith only [hd18braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < (7/2 : ℝ)*lam := by
    linarith only [hd45braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, htr346a, htr347a, htr467b])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr346c, htr367a, htr467a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  rcases m.htr 5 7 8 (by decide) (by decide) with
    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
  ·
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr013a, htr016a, htr134a, htr167a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr016b, htr068a, htr168a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr124a, htr245b, htr257a, htr578a, htr678a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, htr235c, htr237b, htr257c])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc567yz, htr257a, htr258a, htr578c, htr678a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, htr235c, htr238b, htr258c])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc567yz, htr267a, htr268a, htr578a, htr678b])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr578a, htr678a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc567yz, htr357a, htr358a, htr578c, htr678a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, htr236b, htr268a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, htr346b, htr348c, htr368b])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr245c, htr258a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc567yz, htr467a, htr468a, htr578a, htr678b])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    rcases m.htr 0 2 4 (by decide) (by decide) with
      ⟨htr024a, htr024b, htr024c, _, _⟩ | ⟨htr024a, htr024b, htr024c, _, _⟩
    ·
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, htr024a, htr025a, htr245b])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr024c, htr045a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      rcases m.htr 1 3 5 (by decide) (by decide) with
        ⟨htr135a, htr135b, htr135c, _, _⟩ | ⟨htr135a, htr135b, htr135c, _, _⟩
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc123yz, htr013a, htr015a, htr135c, htr235a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc234zy, hc236yx, htr024a, htr026a, htr134a, htr135a, htr235a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr026a, htr027a, htr267b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr026a, htr028a, htr268b])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc123yz, htr015b, htr056a, htr135b, htr235a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr015b, htr057a, htr134a, htr135b, htr578a, htr678a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr015c, htr017b, htr057c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc123yz, htr015b, htr058a, htr135b, htr235a, htr358a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr015c, htr018b, htr058c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, htr012b, htr026a, htr126a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc345xy, htr134c, htr135a, htr146a, htr346a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr146a, htr147a, htr467b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr146a, htr148a, htr468b])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr134a, htr135b, htr157a, htr578a, htr678a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc123yz, htr135b, htr158a, htr235a, htr358a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr017a, htr026a, htr178a, htr267a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr015a, htr024a, htr157a, htr246a, htr467a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc234zy, htr013b, htr036a, htr134a, htr246a, htr346c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc234zy, htr134a, htr136a, htr246a, htr346c])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr015a, htr026a, htr157a, htr267b, htr278a, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd34a, hd67b, htr013b, htr037a, htr134a, htr347c, htr478a, htr678a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc345xy, hc367yz, htr035a, htr037a, htr346a, htr467b, htr478a, htr678a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr035a, htr038a, htr358c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc014yx, hc567yz, htr015a, htr046a, htr157a, htr467b, htr478a, htr678a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd34a, hd67b, htr046a, htr047a, htr346a, htr478a, htr678a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hd34a, hd67b, htr046a, htr048a, htr346a, htr478c, htr678a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc034zy, htr047c, htr078a, htr346a, htr467b, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          rcases m.htr 1 3 7 (by decide) (by decide) with
            ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd67b, htr134a, htr137a, htr347c, htr478a, htr678a]
          ·
            linarith only [hlam, hc345xy, hc367yz, htr135a, htr137a, htr346a, htr467b, htr478a, htr678a]
        ·
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd45b, hd57a, htr024c, htr047a, htr245a, htr478a, htr578a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc457zy, htr047a, htr048a, htr478b, htr578a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr478a, htr578a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc014yx, hc457zy, htr015a, htr046a, htr157a, htr246a, htr247a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc345xy, htr034c, htr035a, htr046a, htr346a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr035a, htr037a, htr357c])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr035a, htr038a, htr358c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hd34a, hd67b, htr046a, htr047b, htr078a, htr346a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc345xy, hc347yz, htr135a, htr137a, htr246a, htr247a, htr346a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc567yz, htr137b, htr138a, htr178a, htr358b, htr578b, htr678a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc234zy, htr046a, htr048a, htr248a, htr346a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd67b, htr134a, htr137a, htr378a, htr678a]
          ·
            linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a]
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, htr013a, htr015a, htr135c])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc157zy, htr013a, htr017a, htr135a, htr357a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc567yz, htr013a, htr018a, htr135a, htr168c, htr357a, htr678c])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr013a, htr026a, htr135a, htr267a, htr357a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr013b, htr035a, htr135a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr013b, htr037a, htr135a, htr357c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr013b, htr038a, htr135a, htr358c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc014yx, hc567yz, htr013a, htr046a, htr135a, htr357a, htr467a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc457zy, hd01b, hd34a, htr013a, htr046a, htr047a, htr135a, htr346a, htr357a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc458zy, hd01b, hd34a, htr013a, htr046a, htr048a, htr135a, htr346a, htr358a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc017yx, hc567yz, htr013a, htr078a, htr135a, htr357a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hd45b, hd57a, htr024a, htr027c, htr078a, htr245a, htr578a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr024a, htr026a, htr126a, htr245a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, htr012b, htr027a, htr127a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr135a, htr137a, htr357c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr135a, htr138a, htr358c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc236yx, htr023c, htr034c, htr046a, htr124b, htr126a, htr146a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc034zy, htr047a, htr146a, htr147a, htr346a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc034zy, htr048a, htr146a, htr148a, htr346a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc236yx, htr023c, htr037c, htr078a, htr126a, htr127b, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        rcases m.htr 2 4 6 (by decide) (by decide) with
          ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
        ·
          linarith only [hlam, htr024c, htr046a, htr246a]
        ·
          linarith only [hlam, hc234zy, htr024a, htr026a, htr246b, htr346a]
    ·
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125xy, htr012c, htr015a, htr024a, htr124a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127xy, htr012c, htr017a, htr024a, htr124a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128xy, htr012c, htr018a, htr024a, htr124a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr024a, htr026a, htr124a, htr267a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234yx, htr023b, htr024a, htr035a, htr235a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr035a, htr037a, htr357c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr035a, htr038a, htr358c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc012zy, htr024c, htr045a, htr124a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, htr035b, htr056a, htr357a, htr567b])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr035b, htr057a, htr358a, htr578b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035b, htr058a, htr358a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc236yx, htr023a, htr024a, htr124a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, htr126a, htr127a, htr267b])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr126a, htr128a, htr268b])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc123yz, htr023a, htr026a, htr136a, htr236b])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr124c, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr146a, htr147a, htr467b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr146a, htr148a, htr468b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr136b, htr156c, htr356b])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd56a, hd67b, htr156a, htr157a, htr578a, htr678a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr156a, htr158a, htr235a, htr358a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc012zy, hc567yz, htr025a, htr124a, htr246a, htr257a, htr467a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc012zy, htr024c, htr046a, htr124a, htr246a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr046a, htr047a, htr467b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr046a, htr048a, htr468b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hc123xy, hc567yz, htr124a, htr135a, htr246a, htr357a, htr467a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc234yx, hc367yz, htr135a, htr137a, htr235a, htr246a, htr467a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc123yz, htr023a, htr027a, htr137a, htr237b])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd34a, hd67b, htr037b, htr078a, htr134a, htr137a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc234yx, hc567yz, htr135a, htr138a, htr235a, htr246a, htr358b, htr467a, htr578b])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc123yz, htr023a, htr028a, htr138a, htr238b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc127xy, hc567yz, htr124a, htr178a, htr246a, htr467a, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc567yz, htr047c, htr078a, htr246a, htr247a, htr467a, htr578a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr246a, htr248a, htr468b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr027c, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      rcases m.htr 3 7 8 (by decide) (by decide) with
        ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
      ·
        linarith only [hlam, hd34a, hd67b, htr134a, htr137a, htr378a, htr678a]
      ·
        linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a]
  ·
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr457a, htr458a, htr578c])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr457b, htr478a, htr578a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    rcases m.htr 0 2 4 (by decide) (by decide) with
      ⟨htr024a, htr024b, htr024c, _, _⟩ | ⟨htr024a, htr024b, htr024c, _, _⟩
    ·
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, htr024a, htr025a, htr245b])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr024c, htr045a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc012yx, hc458yx, htr013a, htr024a, htr134a, htr245a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      rcases m.htr 1 3 5 (by decide) (by decide) with
        ⟨htr135a, htr135b, htr135c, _, _⟩ | ⟨htr135a, htr135b, htr135c, _, _⟩
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc123yz, htr013a, htr015a, htr135c, htr235a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc234zy, hc236yx, htr024a, htr026a, htr134a, htr135a, htr235a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc234zy, hc237yx, htr024a, htr027a, htr134a, htr135a, htr235a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc234zy, hc238yx, htr024a, htr028a, htr134a, htr135a, htr235a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc123yz, htr015b, htr056a, htr135b, htr235a, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr015c, htr016b, htr056c])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, htr012b, htr026a, htr126a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, htr012b, htr027a, htr127a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr012b, htr028a, htr128a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc345xy, htr134c, htr135a, htr146a, htr346a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr146a, htr147a, htr467b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc345xy, htr134c, htr135a, htr148a, htr348a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr146c, htr167a, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, hc347xy, htr134a, htr135a, htr235a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc348xy, htr134a, htr135a, htr235a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr235b, htr257a, htr457a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr257a, htr258a, htr578c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr257b, htr278a, htr578a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr357a, htr457a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123yz, hc178zy, htr013a, htr018a, htr235a, htr357a, htr578a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc123yz, htr015b, htr057a, htr135b, htr235a, htr357a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, htr015c, htr017b, htr057c])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr057a, htr058a, htr578c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr057b, htr078a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr357b, htr578a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc034zy, htr047a, htr134a, htr137a, htr347c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr047c, htr067b, htr467c])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc123yz, htr135b, htr157a, htr235a, htr357a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr157a, htr158a, htr578c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr157b, htr178a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr015a, htr024a, htr157a, htr246a, htr467a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc234zy, htr013b, htr036a, htr134a, htr246a, htr346c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc014yx, hd45b, hd78a, htr015a, htr046a, htr157a, htr245a, htr246a, htr578a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc345xy, htr034c, htr035a, htr046a, htr346a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr035a, htr037a, htr357c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc348xy, htr035a, htr038a, htr134a, htr135a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc345xy, hc478zy, htr046a, htr048a, htr346a, htr357a, htr578a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc234zy, htr134a, htr136a, htr246a, htr346c])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc034zy, htr048a, htr134a, htr138a, htr348c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd45b, hd56a, htr146c, htr168a, htr245a, htr246a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc234zy, htr046a, htr047a, htr247a, htr346a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024c, htr048a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc012yx, hc678zy, htr015a, htr026a, htr157a, htr268a, htr578a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc234zy, htr046b, htr068a, htr246c, htr268a, htr346a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr357a, htr358a, htr578c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr136b, htr168a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        rcases m.htr 4 6 8 (by decide) (by decide) with
          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
        ·
          linarith only [hlam, hc234zy, htr246c, htr268a, htr346a, htr468a]
        ·
          linarith only [hlam, hd45b, hd56a, htr245a, htr246a, htr468a, htr568a]
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, htr013a, htr015a, htr135c])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc156zy, htr013a, htr016a, htr135a, htr356a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hd17b, hd56a, htr013a, htr017a, htr135a, htr356a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hd18b, hd56a, htr013a, htr018a, htr135a, htr356a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, htr013b, htr035a, htr135a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, htr013b, htr036a, htr135a, htr356c])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr015b, htr056a, htr135b, htr356a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc056zy, hd01b, hd34a, htr013a, htr067a, htr135a, htr346a, htr356a, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc017yx, hc345yz, htr013a, htr078a, htr135a, htr457a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr135a, htr136a, htr356c])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr135b, htr156a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr016b, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr246a, htr246b, htr246c, _, _⟩
          linarith only [hlam, hc012yx, hc456zy, htr013a, htr024a, htr135a, htr246a, htr356a])
        obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc234zy, htr024a, htr026a, htr246b, htr346a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr026b, htr027c, htr067b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc345yz, hc347xy, htr013b, htr037a, htr135a, htr245a, htr246a, htr346a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc345yz, hc348xy, htr013b, htr038a, htr135a, htr245a, htr246a, htr346a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc014yx, hc345yz, htr013a, htr046a, htr135a, htr245a, htr246a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc456yx, htr045b, htr046a, htr057a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr057a, htr058a, htr578c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, htr012b, htr026a, htr126a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hd03b, hd56a, htr037a, htr135a, htr137a, htr356a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hd03b, hd56a, htr038a, htr135a, htr138a, htr356a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, htr023c, htr037a, htr237a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr023c, htr038a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, htr025c, htr057a, htr257a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr025c, htr057a, htr258a, htr578c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc025xy, hc167yz, htr026a, htr057a, htr178a, htr267a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr027c, htr078a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc258yx, hc345yz, htr024a, htr025c, htr028a, htr057a, htr245a, htr357a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc345yz, htr024c, htr047a, htr245a, htr357a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr012b, htr028a, htr128a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr014b, htr047a, htr147a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hd01b, hd56a, htr013a, htr135c, htr157a, htr356a, htr357a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc456yx, htr145b, htr146a, htr157a, htr457a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc458yx, htr146a, htr148a, htr245a, htr246a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc234zy, htr046a, htr047a, htr247a, htr346a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr136b, htr168a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc478zy, hd01b, hd34a, htr013a, htr046a, htr048a, htr137a, htr346a, htr378a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc145yz, htr024c, htr048a, htr158a, htr245a, htr458b])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024c, htr048a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc012yx, hc678zy, htr013a, htr026a, htr137a, htr268a, htr378a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc234zy, htr046b, htr068a, htr246c, htr268a, htr346a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc345yz, htr157a, htr158a, htr358a, htr457a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 4 6 8 (by decide) (by decide) with
          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
        ·
          linarith only [hlam, hc234zy, htr246c, htr268a, htr346a, htr468a]
        ·
          linarith only [hlam, hd45b, hd56a, htr245a, htr246a, htr468a, htr568a]
    ·
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125xy, htr012c, htr015a, htr024a, htr124a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc126xy, htr012c, htr016a, htr024a, htr124a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127xy, htr012c, htr017a, htr024a, htr124a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128xy, htr012c, htr018a, htr024a, htr124a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc234yx, htr023b, htr024a, htr035a, htr235a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr035a, htr036a, htr356c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc012zy, htr024c, htr045a, htr124a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, htr035b, htr056a, htr356a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc236yx, htr023a, htr024a, htr124a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc237yx, htr023a, htr024a, htr124a, htr127a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc238yx, htr023a, htr024a, htr124a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr124c, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr146a, htr147a, htr467b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr146c, htr167a, htr467a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc347xy, htr023a, htr024a, htr234b, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc234yx, htr023b, htr024a, htr037a, htr237a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc348xy, htr023a, htr024a, htr234b, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc234yx, htr023b, htr024a, htr038a, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd23b, hd34a, htr023a, htr024a, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr024a, htr026a, htr124a, htr246c, htr467a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc012zy, htr024c, htr046a, htr124a, htr246a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr046a, htr047a, htr467b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046c, htr067a, htr467a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd12a, hd45b, htr024b, htr047b, htr078a, htr124a, htr457a, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc123yz, htr023a, htr026a, htr136a, htr236b])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr136b, htr156c, htr356b])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr023a, htr026a, htr126c, htr168a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr146b, htr148c, htr168b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd14a, hd67b, htr046a, htr048a, htr148a, htr467a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc167yz, hd12a, hd45b, htr124a, htr178a, htr246a, htr457a, htr467a, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr246a, htr247a, htr467b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr024b, htr048a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc012zy, htr026a, htr124a, htr246a, htr267a, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr023a, htr026a, htr268a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc236yx, htr023a, htr026c, htr068a, htr268a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127c, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr134b, htr148a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr136b, htr168a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc367yz, hd12a, hd45b, htr124a, htr246a, htr378a, htr457a, htr467a, htr578a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr467a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc012zy, hc678zy, htr027a, htr124a, htr127c, htr178a, htr246a, htr468a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc123xy, hc678zy, htr124a, htr137a, htr246a, htr378a, htr468a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr135a, htr135b, htr135c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr135a, htr137a, htr237a, htr356a])
      obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc123yz, htr023a, htr025a, htr135a, htr235b])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd34a, hd45b, htr035b, htr057a, htr134a, htr135a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057a, htr058a, htr578c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc234yx, hc368yz, htr137a, htr138a, htr237a, htr246a, htr468a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc123yz, htr023a, htr028a, htr138a, htr238b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc125xy, hc678zy, htr124a, htr157a, htr246a, htr468a, htr578a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc568yz, hd12a, hd45b, htr124a, htr157a, htr158a, htr246a, htr457a, htr468a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr025c, htr057a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      rcases m.htr 3 5 7 (by decide) (by decide) with
        ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
      ·
        linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr357a, htr457a]
      ·
        linarith only [hlam, hd23b, hd56a, htr156a, htr157a, htr235a, htr357a]

theorem shard_198 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr467a : m.d 4 6 + lam ≤ m.d 6 7)
    (htr467b : m.d 4 6 < m.d 4 7)
    (htr467c : m.d 4 7 < m.d 6 7)
    : False :=
  proof_shard_198 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr124a htr124b htr124c htr235a htr235b htr235c htr346a htr346b htr346c htr457a htr457b htr457c htr568a htr568b htr568c htr023a htr023b htr023c htr134a htr134b htr134c htr014a htr014b htr014c htr034a htr034b htr034c htr245a htr245b htr245c htr125a htr125b htr125c htr145a htr145b htr145c htr356a htr356b htr356c htr236a htr236b htr236c htr256a htr256b htr256c htr467a htr467b htr467c

#print axioms shard_198
end Jsp404.NoSatNineDBMTerminal
