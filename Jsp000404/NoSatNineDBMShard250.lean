import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_250 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237b : m.d 2 3 < m.d 2 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238b : m.d 2 3 < m.d 2 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr138b : m.d 1 3 < m.d 1 8)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr146a : m.d 4 6 + lam ≤ m.d 1 4)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < (7/2 : ℝ)*lam := by
    linarith only [hd02braw, hp]
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < (7/2 : ℝ)*lam := by
    linarith only [hd04braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < (7/2 : ℝ)*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc067zy, htr078a, htr567a, htr568a, htr678c])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd01b, hd45a, htr016a, htr168a, htr456a, htr568a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc167zy, htr178a, htr567a, htr568a, htr678c])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hd23a, hd78b, htr012a, htr017a, htr123a, htr178a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr123a, htr124a, htr247a, htr457c, htr567c, htr568a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc234xy, htr014b, htr047a, htr123a, htr124b, htr247a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc234xy, htr123a, htr124b, htr147a, htr247a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc267zy, htr278a, htr567a, htr568a, htr678c])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr234c, htr247a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr567a, htr568a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc367zy, htr378a, htr567a, htr568a, htr678c])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr457a, htr458a, htr567c, htr568b])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr456c, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr457c, htr478a, htr567c, htr568a, htr678c])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc138xy, hc456yz, htr014a, htr018a, htr135a, htr146a, htr356a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hd23a, hd68b, htr012b, htr025a, htr123a, htr235c, htr356a, htr568a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc345yx, hc678xy, htr034a, htr036a, htr356a, htr367a, htr568a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd23a, hd68b, htr035a, htr036a, htr235a, htr356c, htr568a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc023yx, hd23a, hd68b, htr024a, htr035a, htr123a, htr124a, htr356a, htr568a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc234xy, hc268yz, htr024a, htr028a, htr235a, htr356a, htr568a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd23a, hd68b, htr035a, htr037a, htr237a, htr356a, htr568a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, htr035c, htr056a, htr356a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc678xy, htr035c, htr057a, htr356a, htr567b, htr568a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035c, htr058a, htr356a, htr568b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr036c, htr068a, htr356c, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hc234xy, htr024a, htr025a, htr123a, htr125a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr012b, htr028a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc013yx, hc468yz, htr014a, htr035a, htr148a, htr356a, htr568a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc234xy, htr024c, htr048a, htr123a, htr124b, htr148a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr135c, htr156a, htr356a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr015b, htr057a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc013yx, hc678xy, htr016a, htr035a, htr167a, htr356a, htr568a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc468xy, htr046c, htr048a, htr067a, htr146b, htr167a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd23a, hd68b, htr012b, htr026b, htr067a, htr123a, htr567a, htr568a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc234xy, htr024a, htr026a, htr123a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      rcases m.htr 2 4 8 (by decide) (by decide) with
        ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
      ·
        linarith only [hlam, hc458xy, htr024a, htr025a, htr245b, htr248a]
      ·
        linarith only [hlam, hc234xy, htr123a, htr124b, htr148a, htr248a]
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc345zy, hc678xy, htr014a, htr018a, htr145a, htr168c, htr356a, htr567a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd34b, hd45a, htr034a, htr035a, htr356a, htr456a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc345zy, htr035a, htr036a, htr356b, htr456a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc345zy, htr046b, htr067a, htr356a, htr456b, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc345zy, htr036c, htr068a, htr356c, htr456a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr036b, htr038c, htr068b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc345zy, htr246b, htr267a, htr356a, htr456b, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc345zy, htr236c, htr268a, htr356c, htr456a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc458xy, htr345c, htr348a, htr356a, htr456a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hd23a, hd34b, htr123a, htr124a, htr248a, htr348a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc234xy, htr014b, htr048a, htr123a, htr124b, htr248a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc234xy, htr123a, htr124b, htr148a, htr248a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr356a, htr357a, htr567c])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc345zy, htr035a, htr037a, htr357b, htr457a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc678xy, htr356a, htr358a, htr567a, htr568c])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc345zy, htr356c, htr368a, htr456a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc234xy, hc678xy, htr124a, htr126a, htr236a, htr267a, htr368a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hc235yz, hc678xy, htr125a, htr126a, htr268a, htr356a, htr567a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hc678xy, htr126a, htr127a, htr267b, htr268a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr126a, htr128a, htr268b])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc013yx, hc678xy, htr015a, htr036a, htr156a, htr368a, htr567a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc345zy, htr156a, htr157a, htr356a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr156a, htr158a, htr568b])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 2 5 6 (by decide) (by decide) with
        ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd68b, htr123a, htr125a, htr256a, htr568a]
      ·
        linarith only [hlam, hc235xy, htr123a, htr125b, htr156a, htr256a]
  ·
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc137xy, hc456yz, htr014a, htr017a, htr135a, htr146a, htr356a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc138xy, hc456yz, htr014a, htr018a, htr135a, htr146a, htr356a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, htr135c, htr156a, htr356a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, htr235c, htr256a, htr356a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc456yz, htr046a, htr047a, htr467c, htr567a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr568a, htr678b])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc456yz, htr056a, htr058a, htr467a, htr568b, htr678b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc456yz, htr057c, htr078a, htr467a, htr567c, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc456yz, htr146a, htr147a, htr467c, htr567a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr015b, htr057a, htr157a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015b, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, htr017b, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr124c, htr147a, htr247a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc456yz, htr235c, htr257a, htr356a, htr467a, htr567b])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc456yz, htr235c, htr258a, htr356a, htr467a, htr568b, htr678b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc456yz, htr257c, htr278a, htr467a, htr567c, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, htr034c, htr047a, htr347a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc456yz, htr356a, htr357a, htr467a, htr567b])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc456yz, htr356a, htr358a, htr467a, htr568b, htr678b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr456b, htr458a, htr467a, htr568b, htr678b])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr467a, htr468a, htr678b])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc456yz, htr046a, htr048a, htr468c, htr568a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc456yz, htr146a, htr148a, htr468c, htr568a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr124c, htr148a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr034c, htr048a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, htr467c, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr012b, htr025a, htr123a, htr235c, htr357a, htr578a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc013yx, hc478yz, htr014a, htr035a, htr148a, htr357a, htr578a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr024a, htr024b, htr024c, _, _⟩
          linarith only [hlam, hc234xy, htr023c, htr024a, htr035a, htr235a])
        obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, htr024a, htr026a, htr246c])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr024a, htr027a, htr247c])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr024a, htr028a, htr248c])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr035a, htr037a, htr235a, htr378a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr235c, htr357a, htr578a])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc234xy, hc346zy, htr035a, htr036a, htr124a, htr127a, htr235a, htr247b, htr467b])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc234xy, hc456yz, htr035a, htr038a, htr124a, htr127a, htr235a, htr247b, htr358c, htr467b, htr568c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc234xy, hc456yz, htr035b, htr056b, htr067a, htr124a, htr127a, htr235a, htr247b, htr467b, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc456yz, htr067a, htr068a, htr467a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc023zy, htr036a, htr123a, htr126a, htr236c])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        rcases m.htr 1 2 8 (by decide) (by decide) with
          ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
        ·
          linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c]
        ·
          linarith only [hlam, hc234xy, hc278yz, htr124a, htr128a, htr235a, htr357a, htr578a]
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr014b, htr047a, htr146a, htr467c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr046b, htr067a, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr146a, htr147a, htr467c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr146b, htr167a, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, htr124c, htr146a, htr247a, htr467c])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, htr246b, htr267a, htr467a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, htr234c, htr246a, htr347a, htr467c])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, htr346b, htr367a, htr467a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd01b, hd67a, htr014a, htr146a, htr467c, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr457b, htr458c, htr478b])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc067zy, hd01b, hd45a, htr014a, htr078a, htr146a, htr457a, htr467a, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr017b, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc267zy, hd01b, hd45a, htr014a, htr146a, htr278a, htr457a, htr467a, htr578a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, hd01b, hd45a, htr014a, htr146a, htr378a, htr457a, htr467a, htr578a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 1 2 5 (by decide) (by decide) with
            ⟨htr125a, htr125b, htr125c, _, _⟩ | ⟨htr125a, htr125b, htr125c, _, _⟩
          ·
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hc023zy, htr035a, htr123a, htr125a, htr235c])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, htr035a, htr036a, htr356b])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr037a, htr038a, htr378b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr035c, htr056a, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, htr125a, htr126a, htr256b])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr257a, htr578a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc456yz, hc458xy, htr046a, htr048a, htr235c, htr257a, htr356a, htr457a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc235xy, htr015b, htr057a, htr123a, htr125b, htr257a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hc245zy, htr125a, htr127a, htr257b, htr457a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, htr127a, htr128a, htr278b])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hd04b, hd67a, htr048a, htr146a, htr148a, htr467a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hc235xy, htr123a, htr125b, htr157a, htr257a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc567yx, htr156b, htr157a, htr168a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, htr124c, htr148a, htr248a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr126c, htr168a, htr268a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr348a, htr348b, htr348c, _, _⟩
              linarith only [hlam, htr034c, htr048a, htr348a])
            obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, htr235c, htr257a, htr357a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, htr036c, htr068a, htr368a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            rcases m.htr 4 6 8 (by decide) (by decide) with
              ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr467a, htr468a]
            ·
              linarith only [hlam, hc013yx, hc678yz, htr014a, htr037a, htr146a, htr378a, htr468a]
          ·
            have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr025a, htr025b, htr025c, _, _⟩
              linarith only [hlam, htr012b, htr025a, htr125a])
            obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc025zy, hc234xy, htr056a, htr124a, htr125a, htr235a, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr248a, htr248b, htr248c, _, _⟩
              linarith only [hlam, hc458xy, htr124a, htr125a, htr245b, htr248a])
            obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc234xy, htr014b, htr048a, htr123a, htr124b, htr248a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, hc234xy, htr123a, htr124b, htr148a, htr248a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hd01b, hd45a, htr012a, htr125a, htr257a, htr457a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hc245yx, htr124a, htr125c, htr157a, htr257a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, htr157a, htr158a, htr578b])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, htr257a, htr258a, htr578b])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr348a, htr348b, htr348c, _, _⟩
              linarith only [hlam, htr234c, htr248a, htr348a])
            obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨htr024a, htr024b, htr024c, _, _⟩ | ⟨htr024a, htr024b, htr024c, _, _⟩
            ·
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hc234xy, htr023c, htr024a, htr035a, htr235a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, htr035a, htr036a, htr356b])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc234xy, htr023c, htr024a, htr037a, htr237a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, htr037a, htr038a, htr378b])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc245yx, htr024a, htr025c, htr057a, htr257a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, htr057a, htr058a, htr578b])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              rcases m.htr 3 5 7 (by decide) (by decide) with
                ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
              ·
                linarith only [hlam, hc013yx, hc567zy, htr014a, htr035a, htr146a, htr357a, htr467a]
              ·
                linarith only [hlam, hc015yx, hc456yz, htr014a, htr057a, htr146a, htr356a, htr357a]
            ·
              have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr026a, htr026b, htr026c, _, _⟩
                linarith only [hlam, htr024a, htr026a, htr246c])
              obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
              have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr027a, htr027b, htr027c, _, _⟩
                linarith only [hlam, htr024a, htr027a, htr247c])
              obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
              have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr028a, htr028b, htr028c, _, _⟩
                linarith only [hlam, htr024a, htr028a, htr248c])
              obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
              have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr126a, htr126b, htr126c, _, _⟩
                linarith only [hlam, hd02b, hd67a, htr024a, htr124a, htr126a, htr246b, htr467a])
              obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc023zy, htr036a, htr123a, htr126a, htr236c])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd23a, hd56b, htr026b, htr068a, htr123a, htr126a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr268a, htr568a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hd02b, hd67a, htr024a, htr146b, htr168a, htr246c, htr268a, htr467a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, htr036c, htr068a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr268a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc013yx, hc678yz, htr014a, htr037a, htr146a, htr378a, htr468a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hc234xy, hc368zy, htr037a, htr038a, htr237a, htr246a, htr468a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc015yx, hc678yz, htr014a, htr057a, htr146a, htr468a, htr578a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc568zy, hd01b, hd45a, htr014a, htr057a, htr058a, htr146a, htr457a, htr468a])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr127a, htr127b, htr127c, _, _⟩
                linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
              obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
              have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr128a, htr128b, htr128c, _, _⟩
                linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
              obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
              rcases m.htr 3 5 7 (by decide) (by decide) with
                ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd56b, htr056a, htr057a, htr235a, htr357a]
              ·
                linarith only [hlam, hd34b, hd45a, htr034a, htr035a, htr357a, htr457a]
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc567zy, htr014b, htr048a, htr146a, htr467a, htr478c, htr578a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc045zy, htr056a, htr457b, htr478a, htr567c, htr578a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc045zy, htr057a, htr457b, htr478a, htr578a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc567zy, htr057a, htr058a, htr578b, htr678a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc567zy, htr046b, htr068a, htr467a, htr578a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc017yx, hc567zy, htr014a, htr078a, htr146a, htr467a, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc567zy, htr146a, htr148a, htr467a, htr478c, htr578a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, htr015b, htr057a, htr157a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr015b, htr058a, htr158a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc567zy, htr146b, htr168a, htr467a, htr578a, htr678c])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr124c, htr148a, htr248a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hd56b, hd67a, htr235c, htr257a, htr356a, htr578a, htr678a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc234xy, hc567zy, htr012b, htr025a, htr123a, htr246a, htr257a, htr467a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr125a, htr125b, htr125c, _, _⟩
            linarith only [hlam, hc234xy, hc567zy, htr123a, htr125a, htr246a, htr257a, htr467a])
          obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr025b, htr058a, htr258a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc567zy, htr246b, htr268a, htr467a, htr578a, htr678c])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, htr034c, htr048a, htr348a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr578a, htr678a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc013yx, hc567zy, htr014a, htr035a, htr146a, htr357a, htr467a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr024a, htr024b, htr024c, _, _⟩
            linarith only [hlam, hc234xy, htr023c, htr024a, htr035a, htr235a])
          obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr024a, htr026a, htr246c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr024a, htr027a, htr247c])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr024a, htr028a, htr248c])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc234xy, hc367zy, htr035a, htr037a, htr235a, htr246a, htr467a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr037c, htr038b, htr078c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, hd02b, hd67a, htr024a, htr124a, htr126a, htr246b, htr467a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc023zy, htr036a, htr123a, htr126a, htr236c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd34b, hd67a, htr034a, htr037a, htr137c, htr178a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, htr127b, htr178a, htr278a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr035b, htr058a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hc347yx, htr034a, htr037c, htr078a, htr378a]
          ·
            linarith only [hlam, hd34b, hd67a, htr034a, htr037a, htr378a, htr678a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc167zy, hc345zy, htr014a, htr017a, htr145a, htr356a, htr567a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc168zy, hc345zy, htr014a, htr018a, htr145a, htr356a, htr568a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd34b, hd45a, htr034a, htr035a, htr356a, htr456a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc345zy, htr035a, htr036a, htr356b, htr456a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc345zy, htr045a, htr047a, htr356a, htr457c, htr567c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc345zy, htr046b, htr067a, htr356a, htr456b, htr568a, htr678b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc345zy, htr046b, htr068a, htr356a, htr456b, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr046c, htr048b, htr068c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc345zy, htr145a, htr147a, htr356a, htr457c, htr567c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr568a, htr678b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc345zy, htr146b, htr168a, htr356a, htr456b, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr146c, htr148b, htr168c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr124c, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124c, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc345zy, htr246b, htr267a, htr356a, htr456b, htr568a, htr678b])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc345zy, htr246b, htr268a, htr356a, htr456b, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr345c, htr347a, htr356a, htr457c, htr567c])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr034c, htr048a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr356a, htr357a, htr567c])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc345zy, htr035a, htr037a, htr357b, htr457a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr356a, htr358a, htr568c])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, htr356b, htr367a, htr568a, htr678b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr356b, htr368a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc345zy, htr356a, htr456b, htr467a, htr568a, htr678b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc234xy, hc367zy, htr037a, htr038a, htr238a, htr246a, htr467a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc345zy, htr356a, htr456b, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc013yx, hc678yz, htr014a, htr037a, htr146a, htr378a, htr468a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc017yx, hc367zy, htr014a, htr078a, htr146a, htr378a, htr467a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd01b, hd67a, htr014a, htr147a, htr478a, htr678a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc345zy, htr056c, htr067c, htr078a, htr356a, htr457b, htr478a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr056a, htr058a, htr568c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc367zy, htr378a, htr457b, htr458a, htr478a, htr568b, htr678b])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        linarith only [hlam, hc345zy, htr357c, htr378a, htr457a, htr578a]
      ·
        linarith only [hlam, hc345zy, htr356a, htr457b, htr478a, htr567c, htr578a]

theorem shard_250 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237b : m.d 2 3 < m.d 2 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238b : m.d 2 3 < m.d 2 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr138b : m.d 1 3 < m.d 1 8)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr146a : m.d 4 6 + lam ≤ m.d 1 4)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False :=
  proof_shard_250 m htr012a htr012b htr012c htr123a htr123b htr123c htr013a htr013b htr013c htr023a htr023b htr023c htr234a htr234b htr234c htr345a htr345b htr345c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c htr124a htr124b htr124c htr014a htr014b htr014c htr034a htr034b htr034c htr235a htr235b htr235c htr135a htr135b htr135c htr236a htr236b htr236c htr136a htr136b htr136c htr237a htr237b htr237c htr137a htr137b htr137c htr238a htr238b htr238c htr138a htr138b htr138c htr245a htr245b htr245c htr045a htr045b htr045c htr015a htr015b htr015c htr145a htr145b htr145c htr346a htr346b htr346c htr246a htr246b htr246c htr046a htr046b htr046c htr016a htr016b htr016c htr146a htr146b htr146c htr457a htr457b htr457c

#print axioms shard_250
end Jsp404.NoSatNineDBMTerminal
