import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_106 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  obtain ⟨hd28a, hd28braw⟩ := m.hrange 2 8 (by decide)
  have hd28b : m.d 2 8 < (7/2 : ℝ)*lam := by
    linarith only [hd28braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc056yz, htr067a, htr456a, htr457a, htr567b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc156yz, htr167a, htr456a, htr457a, htr567b])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc256yz, htr267a, htr456a, htr457a, htr567b])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc567yx, htr345a, htr347a, htr456a, htr457b])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc678xy, htr456a, htr457a, htr567b, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc567yx, htr456b, htr457a, htr468a, htr568a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hc567yx, htr347c, htr378a, htr456a, htr457c, htr578a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, htr347b, htr348c, htr378b])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  rcases m.htr 0 2 3 (by decide) (by decide) with
    ⟨htr023a, htr023b, htr023c, _, _⟩ | ⟨htr023a, htr023b, htr023c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc124yx, htr012b, htr014a, htr023a, htr123a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc125yx, htr012b, htr015a, htr023a, htr123a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc126yx, htr012b, htr016a, htr023a, htr123a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc127yx, htr012b, htr017a, htr023a, htr123a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc128yx, htr012b, htr018a, htr023a, htr123a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr023a, htr026a, htr123a, htr267a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc012yz, htr023b, htr034a, htr123a, htr234a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hc012yz, htr023b, htr035a, htr123a, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hd12b, hd34a, htr023c, htr035c, htr056a, htr123a, htr345a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hd01a, hd56b, htr015a, htr157a, htr456a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, htr125c, htr127b, htr157c])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hc567yx, htr135c, htr137a, htr157a, htr347c, htr456a, htr457c])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr123c, htr137a, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc012yz, htr023b, htr037a, htr123a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hd12b, hd34a, htr023c, htr037c, htr078a, htr123a, htr347a, htr478a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd12b, hd34a, htr127a, htr278a, htr347a, htr478a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456b])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc012yz, htr023c, htr026a, htr034c, htr046a, htr123a, htr246c])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc567yx, htr045a, htr046a, htr456c, htr457a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc567yx, htr045a, htr047a, htr456a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047a, htr048a, htr478b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc567yx, htr245a, htr247a, htr456a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr247a, htr248a, htr478b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      rcases m.htr 2 3 6 (by decide) (by decide) with
        ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
      ·
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc346xy, htr023a, htr024a, htr234b, htr236a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, htr024a, htr025a, htr245b])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr024a, htr027a, htr247b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr024a, htr028a, htr247b, htr278b])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, htr023c, htr036a, htr236a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc012yz, hc378yz, htr023c, htr024a, htr038a, htr123a, htr247a, htr478a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc012yz, hc567yx, htr023c, htr024a, htr035c, htr057a, htr123a, htr245a, htr456a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr057a, htr058a, htr578b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc346xy, htr123a, htr126a, htr234a, htr236c])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc012yz, hc678yz, htr024a, htr026c, htr068a, htr126a, htr247a, htr478a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        rcases m.htr 1 3 6 (by decide) (by decide) with
          ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
        ·
          linarith only [hlam, hc356xy, htr035b, htr057a, htr135c, htr136a, htr157a]
        ·
          linarith only [hlam, hc012yz, htr023a, htr123c, htr136a, htr236a]
      ·
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc012yz, hc356yz, htr024a, htr123a, htr236a, htr245a, htr456a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc012yz, htr023b, htr036a, htr123a, htr236a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc348xy, hd12b, hd67a, htr023a, htr024a, htr036a, htr038a, htr123a, htr234b, htr367a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, htr123a, htr126a, htr236c])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc248xy, htr024a, htr026a, htr123a, htr128a, htr236c])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, htr123b, htr136a, htr236a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr138a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hc124zy, htr024a, htr026a, htr146a, htr246c])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc567yx, htr145a, htr146a, htr456c, htr457a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc567yx, htr145a, htr147a, htr456a, htr457b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc124yx, hc278yz, htr023a, htr028a, htr123a, htr147a, htr478a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr147a, htr148a, htr478b])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr145c, htr156a, htr456a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd24a, hd56b, htr024a, htr026a, htr126b, htr168a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr147c, htr178a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, htr023c, htr038a, htr238a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hd24a, hd56b, htr024a, htr026a, htr268a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hd12b, hd67a, htr067a, htr068a, htr123a, htr236c, htr268a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc124yx, hc567yx, htr123a, htr145a, htr235a, htr357a, htr456a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr357a, htr358a, htr578b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 3 6 8 (by decide) (by decide) with
          ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
        ·
          linarith only [hlam, hd12b, hd67a, htr123a, htr236c, htr268a, htr367a, htr368a]
        ·
          linarith only [hlam, hc124yx, hc678yz, htr123a, htr147a, htr236a, htr368a, htr478a]
    ·
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr023a, htr024a, htr123a, htr245a, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      rcases m.htr 0 2 5 (by decide) (by decide) with
        ⟨htr025a, htr025b, htr025c, _, _⟩ | ⟨htr025a, htr025b, htr025c, _, _⟩
      ·
        linarith only [hlam, hc012yz, hc567yx, htr025a, htr123a, htr234c, htr245a, htr256a, htr457a]
      ·
        linarith only [hlam, hd12b, hd34a, htr023a, htr025a, htr123a, htr245b, htr345a]
  ·
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, htr023a, htr024a, htr234c])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr025a, htr025b, htr025c, _, _⟩
      linarith only [hlam, htr023a, htr025a, htr235c])
    obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, htr023b, htr034a, htr235a, htr345b])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr023b, htr035a, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    rcases m.htr 2 4 5 (by decide) (by decide) with
      ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
    ·
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr245a, htr246a, htr456b])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc567yx, htr245a, htr247a, htr456a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr023a, htr027a, htr234a, htr247c, htr456a, htr457c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, htr012c, htr027a, htr127a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr247a, htr248a, htr478b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
      ·
        rcases m.htr 2 3 6 (by decide) (by decide) with
          ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc346xy, htr023a, htr026a, htr234a, htr236c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc034zy, htr046a, htr234a, htr236a, htr346c])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr014b, htr016c, htr046b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc567yx, htr045a, htr046a, htr456c, htr457a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, htr014b, htr015c, htr045b])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc567yx, htr045a, htr047a, htr456a, htr457b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, htr014b, htr017c, htr047b])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc178yz, htr014b, htr018a, htr047a, htr478a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr047a, htr048a, htr478b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, htr045c, htr056a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr047c, htr078a, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr012c, htr026a, htr126a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc134zy, htr146a, htr234a, htr236a, htr346c])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc567yx, htr145a, htr146a, htr456c, htr457a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc013xy, hd34a, hd56b, htr014a, htr036a, htr145a, htr234a, htr236a, htr456a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc567yx, htr145a, htr147a, htr456a, htr457b])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr147a, htr148a, htr478b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, htr145c, htr156a, htr456a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hd01a, hd56b, htr015a, htr157a, htr456a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc567yx, htr135c, htr137a, htr157a, htr347c, htr456a, htr457c])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc567yx, htr156b, htr157a, htr168a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr126c, htr128b, htr168c])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hd12b, hd34a, htr023a, htr028a, htr128a, htr234a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr147c, htr178a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc012xy, hc378yz, htr014a, htr023a, htr147a, htr238a, htr478a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc346xy, htr036a, htr038a, htr234a, htr238a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr035c, htr038b, htr058c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hc012xy, hc567yx, htr014a, htr023a, htr145a, htr235c, htr257a, htr456a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc356xy, htr035c, htr036a, htr057a, htr235b, htr257a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc356xy, htr135c, htr136a, htr157a, htr235b, htr257a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc348xy, htr136a, htr138a, htr234a, htr236a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc012xy, hc678yz, htr014a, htr026a, htr147a, htr268a, htr478a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc346xy, htr036c, htr068a, htr234a, htr236b, htr268a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc135zy, htr158a, htr235a, htr236b, htr268a, htr568b])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, htr235b, htr257a, htr357a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr023b, htr037a, htr234a, htr357c, htr456a, htr457a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc346xy, htr036a, htr037a, htr234a, htr237a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr368a, htr568a]
          ·
            linarith only [hlam, hc346xy, htr234a, htr236b, htr268a, htr368a]
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr023a, htr026a, htr236c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hd28b, hd67a, htr023a, htr028a, htr236a, htr367a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr023b, htr036a, htr236a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr023b, htr037a, htr236a, htr367c])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc025yx, hc356yz, htr023a, htr057a, htr236a, htr456a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc067zy, hd12b, hd34a, htr078a, htr123a, htr236a, htr347a, htr367a, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr012c, htr023a, htr126a, htr236c])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr012c, htr028a, htr128a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr123b, htr136a, htr236a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr123b, htr137a, htr236a, htr367c])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc012xy, hc356yz, htr014a, htr023a, htr145a, htr236a, htr456a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc134zy, htr014a, htr015a, htr145b, htr345a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc134zy, htr015c, htr056a, htr145c, htr345a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr015b, htr016c, htr056b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr036c, htr038b, htr068c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr013c, htr038a, htr138a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc567yx, htr145a, htr146a, htr456c, htr457a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc134zy, htr014a, htr017a, htr147b, htr347a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc128yx, hc167zy, htr017a, htr018a, htr123a, htr236a, htr367a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr146a, htr148a, htr468c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, htr145b, htr157a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr016c, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc134zy, hc567yx, htr145a, htr156a, htr157c, htr178a, htr347a, htr457a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, htr236a, htr237a, htr367c])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hd03b, hd67a, htr038a, htr236a, htr238a, htr367a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hc134zy, htr145a, htr235b, htr257a, htr345b, htr457a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc134zy, hc567yx, htr146a, htr256b, htr257a, htr268a, htr345a, htr456a, htr468a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          rcases m.htr 3 5 7 (by decide) (by decide) with
            ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
          ·
            linarith only [hlam, hc134zy, htr145a, htr345b, htr357a, htr457a]
          ·
            linarith only [hlam, hc012xy, hc567yx, htr015a, htr023a, htr156a, htr235a, htr357a]
      ·
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc246xy, htr013a, htr014a, htr123c, htr124b, htr126a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hd12b, hd34a, htr023a, htr026a, htr126a, htr234a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc248xy, htr013a, htr014a, htr123c, htr124b, htr128a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hd12b, hd34a, htr023a, htr028a, htr128a, htr234a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc346xy, htr013a, htr014a, htr124b, htr136a, htr234b])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc134yx, htr013b, htr014a, htr036a, htr136a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr036a, htr037a, htr367c])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, htr136a, htr137a, htr367c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc348xy, htr013a, htr014a, htr124b, htr138a, htr234b])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc134yx, htr013b, htr014a, htr038a, htr138a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr145a, htr345a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc124yx, htr012a, htr014c, htr045a, htr145a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, htr045a, htr046a, htr456b])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc567yx, htr045a, htr047a, htr456a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr047a, htr048a, htr478b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr045c, htr056a, htr456a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr047c, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr145a, htr146a, htr456b])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr014b, htr047a, htr147a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr014b, htr047a, htr148a, htr478b])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr145c, htr156a, htr456a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr147c, htr178a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc124yx, hc567yx, htr123a, htr145a, htr235a, htr357a, htr456a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr237a, htr237b, htr237c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr234a, htr237a, htr357c, htr456a, htr457a])
        obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr357a, htr358a, htr578b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 2 3 6 (by decide) (by decide) with
          ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
        ·
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc134yx, hc135zy, htr014a, htr015a, htr136a, htr235a, htr236a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hd12b, hd34a, htr012a, htr016a, htr136b, htr234a, htr236a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc134yx, hd34a, hd56b, htr014a, htr017a, htr136a, htr147c, htr234a, htr236a, htr456a, htr457c])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc035yx, hd34a, hd56b, htr036a, htr057a, htr234a, htr236a, htr456a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr036b, htr068a, htr234a, htr236a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          rcases m.htr 1 5 7 (by decide) (by decide) with
            ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
          ·
            linarith only [hlam, hc125yx, htr012a, htr015c, htr057a, htr157a]
          ·
            linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr157a, htr357a]
        ·
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc124yx, hc356yz, htr014a, htr015a, htr123a, htr145c, htr236a, htr456a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc124yx, hc167zy, htr014a, htr017a, htr123a, htr236a, htr367a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc025yx, hc356yz, htr023a, htr057a, htr236a, htr456a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          rcases m.htr 1 5 7 (by decide) (by decide) with
            ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
          ·
            linarith only [hlam, hc125yx, htr012a, htr015c, htr057a, htr157a]
          ·
            linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr157a, htr357a]
    ·
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr124b, htr245a, htr345a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc134zy, htr014a, htr015a, htr125b, htr245b, htr345a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc126yx, hc134zy, htr014a, htr016a, htr123a, htr234c, htr245a, htr345a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc127yx, hc134zy, htr014a, htr017a, htr123a, htr234c, htr245a, htr345a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128yx, hc134zy, htr014a, htr018a, htr123a, htr234c, htr245a, htr345a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hc567yx, htr023a, htr026a, htr234c, htr245a, htr256c, htr457a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr026a, htr027a, htr267c])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd28b, hd34a, htr023a, htr028a, htr234c, htr245a, htr345a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc346xy, htr023b, htr036a, htr234c, htr245a, htr345a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr023b, htr037a, htr234c, htr245a, htr347c, htr457c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc348xy, htr023b, htr038a, htr234c, htr245a, htr345a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr024b, htr045a, htr245a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc567yx, htr024b, htr046a, htr245a, htr456c, htr457a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr024b, htr047a, htr245a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr046a, htr048a, htr468c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc034zy, htr045c, htr056a, htr345a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr025b, htr057a, htr245b, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr046b, htr068a, htr468a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc234zy, hc567yx, htr056a, htr057c, htr078a, htr245a, htr347a, htr457a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr012c, htr026a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, htr124b, htr145a, htr245a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr146a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr148a, htr468c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      rcases m.htr 1 5 6 (by decide) (by decide) with
        ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
      ·
        linarith only [hlam, hc012xy, hc567yx, htr015a, htr023a, htr156a, htr234c, htr245a, htr457a]
      ·
        linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a]

theorem shard_106 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    : False :=
  proof_shard_106 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr235a htr235b htr235c htr125a htr125b htr125c htr135a htr135b htr135c htr256a htr256b htr256c htr457a htr457b htr457c

#print axioms shard_106
end Jsp404.NoSatNineDBMTerminal
