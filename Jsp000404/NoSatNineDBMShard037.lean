import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_037 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < (7/2 : ℝ)*lam := by
    linarith only [hd04braw, hp]
  have hd05a := (m.hrange 0 5 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  have hd17a := (m.hrange 1 7 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < (7/2 : ℝ)*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < (7/2 : ℝ)*lam := by
    linarith only [hd37braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < (7/2 : ℝ)*lam := by
    linarith only [hd38braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc057xy, hc057yx, hc057yz, hc057zy⟩ := endpoint_caps m 0 5 7 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr012c, htr024a, htr123a, htr234b, htr345a, htr456a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, htr012b, htr014c, htr024b])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hd05a, hd23b, htr056a, htr234a, htr345a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced124 := (m.htr 1 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr124a, htr124b, htr124c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr123a, htr124a, htr234b, htr345a, htr456a])
  obtain ⟨htr124a, htr124b, htr124c, _, _⟩ := hforced124
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hd01a, hd23b, htr014a, htr145a, htr234a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr012a, htr015a, htr123a, htr145b, htr456a])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr145a, htr146a, htr456c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr145b, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc356zy, htr234a, htr236a, htr345a, htr456a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hd37b, hd56a, htr234a, htr237a, htr345a, htr456a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hd38b, hd56a, htr234a, htr238a, htr345a, htr456a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr234b, htr246a, htr345a, htr456c])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr235b, htr256a, htr345b, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr345a, htr346a, htr456c])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr345b, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr234a, htr345a, htr456a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr234a, htr345a, htr456c, htr467a, htr567a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd23b, hd68a, htr234a, htr345a, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr234a, htr345a, htr456c, htr468a, htr568a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hd56a, hd78b, htr145a, htr147a, htr456a, htr467c, htr678a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr124c, htr147a, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd56a, hd78b, htr345a, htr347a, htr456a, htr467c, htr678a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd23b, hd56a, htr237a, htr378a, htr567a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr467c, htr478a, htr678a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, htr567c, htr578a, htr678a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr012a, htr017a, htr123a, htr147b, htr456a, htr457b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc178yz, hd23b, hd56a, htr012a, htr018a, htr123a, htr456a, htr457a, htr567c, htr678a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc056zy, htr067a, htr456a, htr457a, htr567c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr067a, htr068a, htr678b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr067c, htr078a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc156zy, htr167a, htr456a, htr457a, htr567c])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr167a, htr168a, htr678b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr167c, htr178a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc256zy, htr267a, htr456a, htr457a, htr567c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc023yz, hd56a, hd78b, htr036a, htr234a, htr236b, htr267a, htr345a, htr456a, htr678a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr036b, htr046c, htr346b])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hd23b, hd46a, htr045a, htr046a, htr234a, htr345a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr045a, htr047a, htr234a, htr347a, htr456a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc236yx, htr012a, htr016a, htr123a, htr126b])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc013xy, hd56a, hd78b, htr016a, htr034a, htr167a, htr345a, htr456a, htr678a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc235yx, htr023b, htr025a, htr034a, htr234a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc236yx, htr023b, htr026a, htr034a, htr234a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr026a, htr027a, htr267b])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc278yz, htr026a, htr028a, htr267a, htr678a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr345b, htr456a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr034a, htr037a, htr234a, htr347b, htr456a, htr457b])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr037a, htr038a, htr378b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc468xy, hd23b, hd56a, htr034a, htr036a, htr045a, htr048a, htr234a, htr346b, htr456a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr034c, htr045c, htr057a, htr234a, htr456a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057a, htr058a, htr578b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hc023yz, htr035a, htr123a, htr125a, htr235b])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      rcases m.htr 1 2 7 (by decide) (by decide) with
        ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
      ·
        linarith only [hlam, hd02a, hd78b, htr026a, htr126a, htr127a, htr267c, htr678a]
      ·
        linarith only [hlam, hc023yz, htr037a, htr123a, htr127a, htr237b]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr056a, htr057a, htr234a, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc057zy, hd23b, hd56a, htr078a, htr234a, htr345a, htr457a, htr567a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr145b, htr157a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc157zy, hd23b, hd56a, htr178a, htr234a, htr345a, htr457a, htr567a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr235b, htr257a, htr345b, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc257zy, hd23b, hd56a, htr234a, htr278a, htr345a, htr457a, htr567a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr345b, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      rcases m.htr 1 3 4 (by decide) (by decide) with
        ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
      ·
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hd16a, hd23b, htr012a, htr016a, htr123b, htr134a, htr234a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hd17a, hd23b, htr012a, htr017a, htr123b, htr134a, htr234a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr017a, htr018a, htr178b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc235yx, htr012c, htr025a, htr123b, htr134a, htr234a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc236yx, htr012c, htr026a, htr123b, htr134a, htr234a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc237yx, htr012c, htr027a, htr123b, htr134a, htr234a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr027a, htr028a, htr278b])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, htr013c, htr034a, htr134a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd23b, hd56a, htr013c, htr035a, htr134a, htr234a, htr345b, htr456a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc023yz, htr034b, htr045a, htr234a, htr345a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr045a, htr046a, htr456c])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hc023yz, htr035a, htr123b, htr125a, htr134a, htr234a, htr235b])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc236yx, htr123b, htr126a, htr134a, htr234a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc237yx, htr123b, htr127a, htr134a, htr234a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc378yz, hd01a, hd23b, htr012a, htr013c, htr038a, htr127a, htr134a, htr234a, htr278a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, htr127a, htr128a, htr278b])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, hc023yz, htr035a, htr134a, htr135a, htr234a])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc023yz, htr038a, htr134a, htr138a, htr234a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc023yz, hc568xy, htr035a, htr234a, htr235b, htr258a, htr345a, htr456a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr245c, htr248b, htr258c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hd24b, hd56a, htr045a, htr048a, htr248a, htr456a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr014c, htr048a, htr148a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc256zy, hd01a, hd23b, htr016a, htr167a, htr234a, htr267a, htr345a, htr456a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hd23b, hd56a, htr134a, htr136c, htr167a, htr234a, htr567a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, htr013c, htr036a, htr136a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc023yz, htr036b, htr067a, htr134c, htr146c, htr167a, htr234a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015c, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr014c, htr048a, htr134c, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr035c, htr058a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, htr136c, htr167a, htr367a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hd23b, hd56a, htr013c, htr037a, htr134a, htr234a, htr367b, htr567a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc023yz, htr037a, htr134a, htr137a, htr234a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          linarith only [hlam, hd23b, hd56a, htr015c, htr058a, htr134c, htr145c, htr234a, htr456a, htr458a]
        ·
          linarith only [hlam, hc578yz, hd01a, hd23b, htr012a, htr127a, htr234a, htr278a, htr345a, htr458a]
      ·
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc136yx, hd23b, hd56a, htr012a, htr016a, htr123a, htr134a, htr345a, htr456a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc137yx, hd23b, hd56a, htr012a, htr017a, htr123a, htr134a, htr345a, htr456a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, htr017a, htr018a, htr178b])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr135a, htr135b, htr135c, _, _⟩
          linarith only [hlam, htr134a, htr135a, htr345c])
        obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr134a, htr136a, htr346c])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr134a, htr137a, htr347c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hd23b, hd56a, htr134a, htr138a, htr238a, htr345a, htr456a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        rcases m.htr 1 2 5 (by decide) (by decide) with
          ⟨htr125a, htr125b, htr125c, _, _⟩ | ⟨htr125a, htr125b, htr125c, _, _⟩
        ·
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, htr012c, htr025a, htr125a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc568xy, hd01a, hd23b, htr012a, htr125a, htr234a, htr258a, htr345a, htr456a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr245c, htr248b, htr258c])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hd24b, hd56a, htr145a, htr148a, htr248a, htr456a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hd24b, hd56a, htr248a, htr345a, htr348a, htr456a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr012c, htr028a, htr123a, htr258b, htr456a, htr458a])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc024yz, htr045a, htr245c, htr258a, htr458a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, htr045a, htr046a, htr456c])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, htr045a, htr047a, htr457c])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr045a, htr048a, htr234a, htr348a, htr456a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc056zy, htr068a, htr456a, htr458a, htr568c])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr123a, htr128a, htr258b, htr456a, htr458a])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc156zy, htr168a, htr456a, htr458a, htr568c])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hc256zy, htr268a, htr456a, htr458a, htr568c])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr234a, htr345c, htr358a, htr456a, htr458a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hc023yz, htr035a, htr235c, htr258a, htr358a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr034a, htr034b, htr034c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr345b, htr456a])
            obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc568xy, htr034a, htr036a, htr345a, htr356c, htr358a, htr456a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hc568xy, htr034a, htr037a, htr345a, htr357c, htr358a, htr456a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr034a, htr038a, htr348c])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, hc013xy, hc256zy, htr012a, htr034a, htr126a, htr345a, htr456a])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc023xy, hd23b, hd56a, htr026a, htr034a, htr123a, htr126a, htr345a, htr456a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hc236yx, hc257zy, htr026a, htr027a, htr234a, htr345a, htr457a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc256yx, htr025b, htr026a, htr058a, htr258a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, htr012c, htr027a, htr127a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr015c, htr058a, htr158a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc013xy, hd56a, hd78b, htr016a, htr034a, htr167a, htr345a, htr456a, htr678a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc236yx, htr026b, htr067a, htr123a, htr126c, htr167a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            rcases m.htr 2 6 7 (by decide) (by decide) with
              ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
            ·
              linarith only [hlam, hc236yx, htr123a, htr126c, htr167a, htr267a]
            ·
              linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr267a, htr567a]
          ·
            have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr034a, htr034b, htr034c, _, _⟩
              linarith only [hlam, hc013xy, hc578yz, htr017a, htr034a, htr178a, htr345a, htr458a])
            obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc236yx, htr023b, htr026a, htr034a, htr234a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, hc237yx, htr023b, htr027a, htr034a, htr234a])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, htr027a, htr028a, htr278b])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr345b, htr456a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hc023yz, hc578yz, htr037a, htr234a, htr345a, htr378a, htr458a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc023yz, htr034b, htr045a, htr234a, htr345a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc578yz, htr045a, htr046a, htr458a, htr467a, htr678a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, htr045a, htr048a, htr458c])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr045b, htr058a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hc578yz, hd01a, hd23b, htr012a, htr127a, htr234a, htr278a, htr345a, htr458a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, hc237yx, hc256zy, htr126a, htr127a, htr234a, htr345a, htr456a])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc023yz, htr036a, htr123a, htr126a, htr236b])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr026c, htr067a, htr123a, htr126a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr067a, htr068a, htr678b])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, hc237yx, hc258zy, htr127a, htr128a, htr234a, htr345a, htr458a])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hc023yz, htr038a, htr123a, htr128a, htr238b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc136yx, hc578yz, htr134a, htr167a, htr345a, htr458a, htr678a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc568yz, hd23b, hd56a, htr167a, htr168a, htr234a, htr345a, htr458a, htr567a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            rcases m.htr 2 6 7 (by decide) (by decide) with
              ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
            ·
              linarith only [hlam, hc236yx, htr123a, htr126c, htr167a, htr267a]
            ·
              linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr267a, htr567a]
        ·
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc023yz, htr035a, htr123a, htr125a, htr235b])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr345b, htr456a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc023xy, hd23b, hd56a, htr025a, htr034a, htr123a, htr125a, htr345a, htr456a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr025a, htr026a, htr256c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr025a, htr027a, htr257c])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd23b, hd56a, htr034a, htr038a, htr238a, htr345a, htr456a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc013xy, hc568xy, htr015a, htr034a, htr158a, htr345a, htr456a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hd23b, hd56a, htr056a, htr058a, htr123a, htr125c, htr158a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr025c, htr028b, htr058c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr024b, htr025c, htr048b, htr058c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc013xy, hd56a, hd78b, htr016a, htr034a, htr167a, htr345a, htr456a, htr678a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc236yx, htr026b, htr067a, htr123a, htr125c, htr156c, htr167a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr024c, htr048a, htr248a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc235yx, htr123a, htr125c, htr158a, htr258a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc568yz, hd23b, hd56a, htr067a, htr068a, htr123a, htr125a, htr258a, htr567a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr016c, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          rcases m.htr 2 6 7 (by decide) (by decide) with
            ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
          ·
            linarith only [hlam, hc236yx, htr123a, htr125c, htr156c, htr167a, htr267a]
          ·
            linarith only [hlam, hd23b, hd56a, htr123a, htr125a, htr256c, htr267a, htr567a]
  ·
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc056zy, htr067a, htr456a, htr457a, htr567c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc567xy, htr145a, htr147a, htr456a, htr457c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr012a, htr017a, htr123a, htr147b, htr456a, htr457b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc156zy, htr167a, htr456a, htr457a, htr567c])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr124c, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc256zy, htr267a, htr456a, htr457a, htr567c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc567xy, htr345a, htr347a, htr456a, htr457c])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr234a, htr345c, htr357a, htr456a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc023yz, hc567xy, htr035a, htr234a, htr345a, htr357a, htr456a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr345b, htr456a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc136yx, hd23b, hd56a, htr012a, htr013c, htr016a, htr034a, htr123a, htr345a, htr456a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc138yx, hd23b, hd56a, htr012a, htr013c, htr018a, htr034a, htr123a, htr345a, htr456a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc567xy, htr034a, htr036a, htr345a, htr356c, htr357a, htr456a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr034a, htr037a, htr347c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr034a, htr038a, htr238a, htr345a, htr456a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr034b, htr045a, htr347a, htr457b])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr034b, htr047a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc013xy, hc256zy, htr012a, htr034a, htr126a, htr345a, htr456a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc023xy, hd23b, hd56a, htr026a, htr034a, htr123a, htr126a, htr345a, htr456a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr134a, htr134b, htr134c, _, _⟩
        linarith only [hlam, htr013c, htr034a, htr134a])
      obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc013xy, hc567xy, htr015a, htr034a, htr157a, htr345a, htr456a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr123a, htr125c, htr157a, htr456a, htr457a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, htr012c, htr025a, htr125a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc246yx, htr025b, htr026a, htr057a, htr124c, htr145c, htr157a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc458xy, htr045c, htr048a, htr057a, htr457a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc568xy, htr057a, htr058a, htr456a, htr457a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd56a, hd67b, htr057b, htr078a, htr456a, htr457a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015c, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr017c, htr078a, htr178a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr024c, htr048a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr125c, htr157a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr012c, htr027a, htr123a, htr257b, htr456a, htr457a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc236yx, htr026a, htr027a, htr123a, htr127a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr015c, htr058a, htr125c, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr268a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc236yx, htr016c, htr068a, htr123a, htr126c, htr268a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc236yx, htr123a, htr126c, htr168a, htr268a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr027c, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd04b, hd56a, htr048a, htr345a, htr348a, htr456a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc015xy, hc568yz, htr016a, htr057a, htr168a, htr357a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr012c, htr028a, htr123a, htr258b, htr345b, htr358a, htr456a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc236yx, htr026a, htr028a, htr123a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, htr345b, htr358a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc013xy, hc678zy, htr016a, htr034a, htr168a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr237a, htr378a, htr456a, htr457b, htr478a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        linarith only [hlam, hd56a, hd67b, htr456a, htr457a, htr578a, htr678a]
      ·
        linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr056a, htr057a, htr234a, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr145a, htr147a, htr457c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc567yz, htr145a, htr148a, htr457a, htr468c, htr678c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr145b, htr157a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr234b, htr247a, htr345a, htr457c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124c, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr235b, htr257a, htr345b, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc237yx, hc567yz, htr234a, htr278a, htr345a, htr457a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr257c, htr258b, htr278c])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr345a, htr347a, htr457c])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc567yz, htr345a, htr348a, htr457a, htr468c, htr678c])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr345b, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr234a, htr345a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr012c, htr025a, htr123a, htr257c, htr278a, htr578a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr012c, htr027a, htr123a, htr278a, htr578a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, htr012b, htr017c, htr027b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc236yx, hc257zy, htr026a, htr027a, htr234a, htr345a, htr457a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, htr012b, htr016c, htr026b])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc257zy, htr027a, htr028a, htr278b, htr578a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr012b, htr018c, htr028b])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567yz, htr057a, htr058a, htr578c, htr678a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr123a, htr125a, htr257c, htr278a, htr578a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr123a, htr127a, htr278a, htr578a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc013xy, hc257zy, htr012a, htr034a, htr127a, htr345a, htr457a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr345b, htr456a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc023yz, htr034b, htr045a, htr234a, htr345a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr045a, htr046a, htr456c])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr045a, htr047a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr045a, htr048a, htr234a, htr348a, htr456a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc236yx, hc257zy, htr126a, htr127a, htr234a, htr345a, htr457a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc257zy, htr127a, htr128a, htr278b, htr578a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015c, htr058a, htr158a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc567yz, hd01a, hd23b, htr017a, htr178a, htr234a, htr345a, htr457a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      rcases m.htr 2 6 7 (by decide) (by decide) with
        ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
      ·
        linarith only [hlam, hc567yz, hd01a, hd23b, htr012a, htr126a, htr234a, htr267a, htr345a, htr457a]
      ·
        linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a]

theorem shard_037 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_037 m htr012a htr012b htr012c htr123a htr123b htr123c htr013a htr013b htr013c htr023a htr023b htr023c htr234a htr234b htr234c htr345a htr345b htr345c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c

#print axioms shard_037
end Jsp404.NoSatNineDBMTerminal
