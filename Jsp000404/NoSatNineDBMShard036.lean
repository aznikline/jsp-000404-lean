import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_036 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  have hd07a := (m.hrange 0 7 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd18a := (m.hrange 1 8 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < (7/2 : ℝ)*lam := by
    linarith only [hd23braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd23b, hd78a, htr234a, htr345c, htr356a, htr567a, htr678a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd23b, hd78a, htr234a, htr345a, htr457a, htr567b, htr678a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, htr567a, htr568a, htr678c])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, htr567b, htr578a, htr678a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  rcases m.htr 1 2 4 (by decide) (by decide) with
    ⟨htr124a, htr124b, htr124c, _, _⟩ | ⟨htr124a, htr124b, htr124c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, htr012a, htr014a, htr124b])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr024a, htr024b, htr024c, _, _⟩
      linarith only [hlam, htr012c, htr024a, htr124a])
    obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, hd01a, hd23b, htr012a, htr124b, htr145a, htr234a, htr345a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045zy, htr056a, htr345a, htr346a, htr456c])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc456xy, htr234a, htr236a, htr345a, htr346c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc245zy, htr256a, htr345a, htr346a, htr456c])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc456xy, htr345c, htr346a, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc568yx, htr345a, htr346a, htr456c, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc456xy, htr345c, htr346a, htr358a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc378zy, hc456xy, htr234a, htr238a, htr345a, htr467a, htr678a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc456xy, htr236b, htr267a, htr345a, htr346b, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr012c, htr026a, htr123a, htr267a, htr678a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, htr012b, htr016c, htr026b])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr267a, htr678a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr236c, htr237b, htr267c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr267a, htr268a, htr678c])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr267b, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc023yz, hc578zy, htr035a, htr236a, htr358a, htr367a, htr678a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc456xy, htr034a, htr035a, htr345b, htr346a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc456xy, htr034a, htr036a, htr345a, htr346c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc135yx, hd23b, hd78a, htr012a, htr013c, htr015a, htr036a, htr123a, htr367a, htr678a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc137yx, hd23b, hd78a, htr012a, htr013c, htr017a, htr036a, htr123a, htr367a, htr678a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc138yx, hd23b, hd78a, htr012a, htr013c, htr018a, htr036a, htr123a, htr367a, htr678a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr036a, htr037a, htr367c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc378zy, htr036a, htr038a, htr367a, htr678a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, htr034b, htr045a, htr345a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr036b, htr067a, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr036b, htr068a, htr367a, htr678c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr037b, htr078a, htr367b, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr125a, htr125b, htr125c, _, _⟩
        linarith only [hlam, hc013xy, hd56b, hd78a, htr012a, htr036a, htr125a, htr256a, htr367a, htr678a])
      obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc023xy, hd23b, hd78a, htr025a, htr036a, htr123a, htr125a, htr367a, htr678a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc235yx, hc278zy, htr025a, htr028a, htr236a, htr367a, htr678a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc235yx, hc478zy, htr024b, htr025a, htr048a, htr236a, htr367a, htr678a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr012c, htr028a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr134a, htr134b, htr134c, _, _⟩
        linarith only [hlam, htr013c, htr034a, htr134a])
      obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr137a, htr367c])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc013xy, hc578zy, htr015a, htr036a, htr158a, htr367a, htr678a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc235yx, hc456xy, htr024b, htr025a, htr046a, htr123a, htr125c, htr158a, htr458a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr046a, htr047a, htr467c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc235yx, htr025b, htr058a, htr123a, htr125c, htr158a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr146a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr147a, htr467c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr016c, htr036b, htr167a, htr367a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc013xy, htr017a, htr036a, htr178a, htr367a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr124c, htr246a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr014c, htr046a, htr124c, htr247a, htr467c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124a, htr125c, htr158a, htr248a, htr458c])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr257a, htr567b, htr678a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc235yx, htr015c, htr057a, htr123a, htr125c, htr257a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc568yx, htr057a, htr058a, htr156a, htr157a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      rcases m.htr 2 5 8 (by decide) (by decide) with
        ⟨htr258a, htr258b, htr258c, _, _⟩ | ⟨htr258a, htr258b, htr258c, _, _⟩
      ·
        linarith only [hlam, hc235yx, htr123a, htr125c, htr158a, htr258a]
      ·
        linarith only [hlam, hd23b, hd45a, htr123a, htr125a, htr258a, htr458a]
    ·
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd01a, hd23b, htr012a, htr124b, htr146a, htr234a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr234a, htr236a, htr346c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc378zy, hc456yz, htr234a, htr238a, htr346a, htr567a, htr678a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr234b, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc237yx, hc456yz, htr234a, htr278a, htr346a, htr567a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr234a, htr346a, htr467a, htr678a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr567a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc456yz, htr146a, htr147a, htr467c, htr567a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc456yz, htr156a, htr157a, htr467a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc456yz, htr147b, htr178a, htr467b, htr567a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr012a, htr017a, htr123a, htr178a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr147c, htr148b, htr178c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr124c, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr234c, htr237b, htr247c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr124c, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr567a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc456yz, htr256a, htr257a, htr467a, htr567b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr235b, htr257a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc456yz, htr347b, htr378a, htr467b, htr567a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr347c, htr348b, htr378c])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc568yx, htr456b, htr458a, htr467a, htr567a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd07a, hd23b, htr078a, htr234a, htr347a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      rcases m.htr 1 3 4 (by decide) (by decide) with
        ⟨htr134a, htr134b, htr134c, _, _⟩ | ⟨htr134a, htr134b, htr134c, _, _⟩
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd15a, hd23b, htr012a, htr015a, htr123b, htr134a, htr234a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr015a, htr016a, htr156b])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hd18a, hd23b, htr012a, htr018a, htr123b, htr134a, htr234a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr025a, htr025b, htr025c, _, _⟩
          linarith only [hlam, hc235yx, htr012c, htr025a, htr123b, htr134a, htr234a])
        obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, htr025a, htr026a, htr256b])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, htr025a, htr027a, htr257b])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc238yx, htr012c, htr028a, htr123b, htr134a, htr234a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, htr013c, htr034a, htr134a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr013c, htr037a, htr134a, htr234a, htr378a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc023yz, htr034b, htr045a, htr234a, htr345a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc023yz, htr034b, htr046a, htr234a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc023yz, htr034b, htr047a, htr234a, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr047a, htr048a, htr478c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr125a, htr125b, htr125c, _, _⟩
          linarith only [hlam, hc235yx, htr123b, htr125a, htr134a, htr234a])
        obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc356yz, hd01a, hd23b, htr012a, htr013c, htr036a, htr125a, htr134a, htr234a, htr256a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc016xy, hc456yz, htr012a, htr067a, htr125a, htr256a, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, htr125a, htr126a, htr256b])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, htr125a, htr127a, htr257b])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc238yx, htr123b, htr128a, htr134a, htr234a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr136a, htr136b, htr136c, _, _⟩
          linarith only [hlam, hc023yz, htr036a, htr134a, htr136a, htr234a])
        obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc023yz, htr037a, htr134a, htr137a, htr234a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc023yz, htr036b, htr067a, htr134c, htr146c, htr167a, htr234a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc568yx, htr156b, htr158a, htr167a, htr567a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 2 5 8 (by decide) (by decide) with
          ⟨htr258a, htr258b, htr258c, _, _⟩ | ⟨htr258a, htr258b, htr258c, _, _⟩
        ·
          linarith only [hlam, hc578zy, hd01a, hd23b, htr012a, htr125a, htr234a, htr258a, htr347a, htr478a]
        ·
          linarith only [hlam, hd01a, hd56b, htr015a, htr158a, htr256a, htr258a]
      ·
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc135yx, hd23b, hd78a, htr012a, htr015a, htr123a, htr134a, htr347a, htr478a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, htr015a, htr016a, htr156b])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc138yx, hd23b, hd78a, htr012a, htr018a, htr123a, htr134a, htr347a, htr478a])
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
          linarith only [hlam, htr134a, htr138a, htr347c, htr378c])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        rcases m.htr 1 2 5 (by decide) (by decide) with
          ⟨htr125a, htr125b, htr125c, _, _⟩ | ⟨htr125a, htr125b, htr125c, _, _⟩
        ·
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, htr012c, htr025a, htr125a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr012c, htr026a, htr125a, htr256b])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr012c, htr027a, htr125a, htr257b])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc238yx, hc456yz, htr012c, htr028a, htr125a, htr234a, htr256a, htr346a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc013xy, hc456yz, htr012a, htr034a, htr125a, htr256a, htr346a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc356yz, hd01a, hd23b, htr012a, htr034a, htr036a, htr125a, htr234a, htr256a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr034a, htr037a, htr234a, htr378a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc023yz, htr034b, htr045a, htr234a, htr345a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc023yz, htr034b, htr046a, htr234a, htr346a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc456yz, hd01a, hd23b, htr012a, htr046a, htr047a, htr125a, htr234a, htr256a, htr347a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr047a, htr048a, htr478c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc016xy, hc456yz, htr012a, htr067a, htr125a, htr256a, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr125a, htr126a, htr256b])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, htr125a, htr127a, htr257b])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hd02a, hd56b, htr028a, htr125a, htr128a, htr256a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc023yz, hc456yz, htr036a, htr136b, htr167a, htr234a, htr346a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr167a, htr168a, htr678c])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc578zy, hd01a, hd23b, htr012a, htr125a, htr234a, htr258a, htr347a, htr478a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc023yz, hc456yz, htr035b, htr058a, htr234a, htr256a, htr258a, htr346a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc056yz, htr068a, htr256a, htr258a, htr568b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hd01a, hd56b, htr015a, htr158a, htr256a, htr258a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, htr126c, htr167a, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr035b, htr058a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc235zy, htr035a, htr038a, htr258a, htr358c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hc023yz, htr036a, htr124c, htr146c, htr167a, htr234c, htr367a]
          ·
            linarith only [hlam, hc023yz, htr036b, htr067a, htr234a, htr346c, htr367a]
        ·
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc023yz, htr035a, htr123a, htr125a, htr235b])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc024yz, htr045a, htr124a, htr125a, htr235b, htr345b])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hd23b, hd45a, htr045a, htr046a, htr234a, htr346a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd23b, hd45a, htr045a, htr047a, htr234a, htr347a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr047a, htr048a, htr478c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, hc235yx, hc278zy, htr125a, htr128a, htr234a, htr347a, htr478a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc023yz, htr038a, htr123a, htr128a, htr238b])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hd23b, hd45a, htr123a, htr125a, htr258a, htr458a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc235yx, htr015c, htr058a, htr123a, htr125c, htr258a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc235yx, htr123a, htr125c, htr158a, htr258a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc013xy, hc578zy, htr015a, htr034a, htr158a, htr347a, htr478a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr025a, htr025b, htr025c, _, _⟩
            linarith only [hlam, hc235yx, htr023b, htr025a, htr034a, htr234a])
          obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr025a, htr026a, htr256b])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr025a, htr027a, htr257b])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr025a, htr028a, htr258b])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr034a, htr037a, htr234a, htr378a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hc023yz, htr037a, htr123a, htr127a, htr237b])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc235yx, hc356yz, htr034a, htr036a, htr125a, htr127a, htr234a, htr257c, htr567c])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc235yx, hc456yz, htr034c, htr046c, htr067a, htr125a, htr127a, htr234a, htr257c, htr467a, htr567c])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr036b, htr038c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, hc023yz, htr036a, htr123a, htr126a, htr236b])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hd35a, hd56b, htr035a, htr036a, htr136b, htr167a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, htr126c, htr167a, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc235yx, htr034a, htr035a, htr234a, htr258a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            linarith only [hlam, hd35a, hd56b, htr035a, htr036a, htr367a, htr567a]
          ·
            linarith only [hlam, hc023yz, htr036b, htr067a, htr234a, htr346c, htr367a]
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hc234yx, htr012a, htr014a, htr123a, htr124b])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hc023yz, htr034a, htr123a, htr124a, htr234b])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, htr034a, htr035a, htr345c])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, htr034b, htr045a, htr345a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr014c, htr045c, htr056a, htr123a, htr124c, htr567a, htr678a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced125 := (m.htr 1 2 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr125a, htr125b, htr125c, _, _⟩
      linarith only [hlam, htr124a, htr125a, htr245c])
    obtain ⟨htr125a, htr125b, htr125c, _, _⟩ := hforced125
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc235yx, htr012a, htr015a, htr123a, htr125b])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, htr015b, htr016c, htr056b])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr124b, htr145a, htr234b, htr345a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr123a, htr125c, htr156a, htr567a, htr678a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hc346xy, htr123a, htr124a, htr234b, htr236a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr034a, htr036a, htr236a, htr345a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013c, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hc347xy, htr123a, htr124a, htr234b, htr237a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr034a, htr037a, htr237a, htr345a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, hc348xy, htr123a, htr124a, htr234b, htr238a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr034a, htr038a, htr238a, htr345a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr013c, htr038a, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr125b, htr156a, htr256a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr123a, htr124a, htr245c, htr257a, htr567b, htr678a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc235yx, htr014c, htr045c, htr057a, htr123a, htr124c, htr257a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, htr015b, htr017c, htr057b])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc235yx, htr123a, htr125c, htr157a, htr257a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd01a, hd56b, htr017a, htr178a, htr567a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc237yx, hd45a, hd56b, htr123a, htr124a, htr234b, htr278a, htr345a, htr567a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr235b, htr257a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd23b, hd58a, htr123a, htr124a, htr234b, htr345a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr123a, htr124a, htr245c, htr258a, htr458a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc235yx, htr014c, htr045c, htr058a, htr123a, htr124c, htr258a])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, htr015b, htr018c, htr058b])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc235yx, htr123a, htr125c, htr158a, htr258a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, htr235b, htr258a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc013xy, hc578zy, htr015a, htr036a, htr158a, htr367a, htr678a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc356yz, htr037b, htr078a, htr367b, htr567a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc013xy, hc457yz, htr015a, htr037a, htr157a, htr378a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr123a, htr124a, htr247a, htr478a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc234yx, htr014c, htr047a, htr123a, htr124c, htr247a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc457xy, htr124a, htr127a, htr234b, htr247c, htr345a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, htr127a, htr128a, htr278c])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc234yx, htr123a, htr124c, htr147a, htr247a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr234b, htr247a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc457xy, htr046a, htr047a, htr345a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc456xy, htr046c, htr067a, htr345a, htr346b, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hc457xy, htr146a, htr147a, htr345a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc456xy, htr146c, htr167a, htr345a, htr346b, htr367a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hd45a, hd56b, htr124a, htr126b, htr167a, htr234b, htr345a, htr567a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr246a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr126b, htr167a, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a]
      ·
        linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a]
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr034b, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc457xy, htr046c, htr047a, htr067a, htr345b, htr356b, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc235yx, hc456yz, htr025b, htr056b, htr067a, htr123a, htr124a, htr234b, htr346a, htr567a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, htr024a, htr025a, htr245c])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr025a, htr027a, htr257b])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr025a, htr028a, htr258b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc456yz, hd23b, hd68a, htr067a, htr068a, htr123a, htr124a, htr234b, htr346a, htr567a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, hc246zy, htr124a, htr126a, htr234b, htr346a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr234b, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      rcases m.htr 1 6 7 (by decide) (by decide) with
        ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
      ·
        linarith only [hlam, hc456yz, hd01a, hd23b, htr016a, htr123a, htr124a, htr167a, htr234b, htr346a, htr567a]
      ·
        linarith only [hlam, hc457xy, htr146c, htr147a, htr167a, htr345b, htr356b, htr367a]

theorem shard_036 {lam p : ℝ} (m : NineModel lam p)
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
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    : False :=
  proof_shard_036 m htr012a htr012b htr012c htr123a htr123b htr123c htr013a htr013b htr013c htr023a htr023b htr023c htr234a htr234b htr234c htr345a htr345b htr345c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr567a htr567b htr567c htr678a htr678b htr678c

#print axioms shard_036
end Jsp404.NoSatNineDBMTerminal
