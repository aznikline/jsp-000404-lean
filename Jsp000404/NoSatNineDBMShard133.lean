import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_133 {lam p : ℝ} (m : NineModel lam p)
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
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr458a : m.d 4 5 + lam ≤ m.d 5 8)
    (htr458b : m.d 4 5 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr358a : m.d 3 5 + lam ≤ m.d 5 8)
    (htr358b : m.d 3 5 < m.d 3 8)
    (htr358c : m.d 3 8 < m.d 5 8)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  have hd07a := (m.hrange 0 7 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < (7/2 : ℝ)*lam := by
    linarith only [hd13braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045zy, htr056a, htr345a, htr346a, htr456c])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc456xy, htr123b, htr136a, htr234a, htr345a, htr346c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc456xy, htr234a, htr236a, htr345a, htr346c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr246a, htr345a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc012yz, hc456xy, htr024a, htr123a, htr234a, htr246a, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr023a, htr023b, htr023c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
      obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc456xy, htr023a, htr025a, htr234a, htr245c, htr246a, htr345a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr023a, htr026a, htr236c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr027a, htr127a, htr234a, htr345a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr028a, htr128a, htr234a, htr345a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr023b, htr034a, htr236a, htr346b])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr023b, htr036a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc456xy, htr245c, htr246a, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc456xy, htr245c, htr246a, htr258a, htr458a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc456xy, htr026b, htr067a, htr236b, htr345a, htr346b, htr467a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr036c, htr037b, htr067c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hd03b, hd45a, htr037a, htr234a, htr237a, htr345a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc456xy, htr236b, htr267a, htr345a, htr346b, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678xy, hd12b, hd45a, htr123a, htr236a, htr345a, htr346a, htr367a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc456xy, htr026b, htr068a, htr236b, htr345a, htr346b, htr468a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr036c, htr038b, htr068c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hd03b, hd45a, htr038a, htr234a, htr238a, htr345a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc456xy, htr236b, htr268a, htr345a, htr346b, htr468a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr123a, htr236a, htr345a, htr346a, htr368a, htr456c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc678yz, hd12b, hd45a, htr045a, htr047a, htr123a, htr236a, htr368a, htr457c, htr578a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc025yx, hc678yz, htr023a, htr057a, htr236a, htr368a, htr578a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc456xy, htr045c, htr046a, htr057a, htr457a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr014a, htr014b, htr014c, _, _⟩
          linarith only [hlam, hd12b, hd45a, htr012a, htr014c, htr046a, htr345a, htr346a])
        obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr046a, htr048a, htr468c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc568zy, hd12b, hd45a, htr057a, htr058a, htr123a, htr236a, htr368a, htr457a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc045zy, htr057c, htr078a, htr457a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr014c, htr046a, htr146a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hd12b, hd45a, htr012a, htr016a, htr146b, htr345a, htr346a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc045zy, htr014c, htr046a, htr057a, htr147a, htr345a, htr346a, htr457c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc045zy, htr014c, htr046a, htr058a, htr148a, htr345a, htr346a, htr458c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc125yx, hc678yz, htr123a, htr157a, htr236a, htr368a, htr578a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr157a, htr457a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc145zy, htr015a, htr017a, htr157b, htr457a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc128yx, hc145zy, htr015a, htr018a, htr123a, htr234a, htr345a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015c, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 1 7 8 (by decide) (by decide) with
          ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
        ·
          linarith only [hlam, hc012xy, hc678yz, htr017a, htr023a, htr178a, htr236a, htr368a]
        ·
          linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a]
      ·
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hd56b, hd67a, htr056a, htr057a, htr578a, htr678a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc567zy, htr057a, htr058a, htr578b, htr678a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc027yx, hc567zy, htr023a, htr078a, htr236a, htr367a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hd56b, hd67a, htr156a, htr157a, htr578a, htr678a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr015a, htr015b, htr015c, _, _⟩
          linarith only [hlam, hc012xy, hc567zy, htr015a, htr023a, htr157a, htr236a, htr367a])
        obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc125yx, hc167zy, htr015a, htr017a, htr123a, htr236a, htr367a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc125yx, hc168zy, htr015a, htr018a, htr123a, htr236a, htr368a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015b, htr058a, htr158a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 1 7 8 (by decide) (by decide) with
          ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
        ·
          linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a]
        ·
          linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr045a, htr046a, htr123a, htr234a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr123b, htr136a, htr234a, htr346c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc456yz, htr123b, htr137a, htr234a, htr346a, htr357c, htr567c])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr234b, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc126yx, hc456yz, htr123a, htr167a, htr234a, htr346a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr146c, htr147b, htr167c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr234a, htr236a, htr346c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc456yz, htr234a, htr237a, htr346a, htr357c, htr567c])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, htr234b, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr123a, htr234a, htr346a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr012a, htr014a, htr146c, htr167a, htr467a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr167a, htr467a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125yx, hc146zy, htr015a, htr016a, htr123a, htr234a, htr346a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc146zy, htr016a, htr017a, htr167b, htr467a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128yx, hc146zy, htr016a, htr018a, htr123a, htr234a, htr346a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456yz, htr046a, htr047a, htr467c, htr567a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr567a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc456yz, hd12b, hd45a, htr056a, htr058a, htr123a, htr234a, htr346a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc146zy, htr017c, htr078a, htr167c, htr467a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc468xy, htr146c, htr148a, htr167a, htr467a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr134c, htr138b, htr148c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr023a, htr023b, htr023c, _, _⟩
        linarith only [hlam, hc012xy, hc456yz, htr015a, htr023a, htr156a, htr234a, htr346a])
      obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc012yz, hc456yz, htr025a, htr123a, htr125b, htr156a, htr234a, htr346a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc012yz, htr023b, htr034a, htr123a, htr234a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr034a, htr036a, htr346c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr034a, htr037a, htr123a, htr237a, htr345a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hd13b, hd45a, htr034a, htr038a, htr138a, htr345a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc456yz, htr156a, htr157a, htr467a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc456yz, hd12b, hd45a, htr123a, htr156a, htr158a, htr234a, htr346a, htr458a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc146zy, htr167c, htr178a, htr467a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr023c, htr038a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr024c, htr047a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc012yz, htr024a, htr124c, htr148a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr045a, htr048a, htr123a, htr234c, htr248a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr023a, htr025a, htr123a, htr256a, htr467a, htr567a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc125yx, htr023a, htr025a, htr123a, htr157a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc125yx, htr023a, htr025a, htr123a, htr158a, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127b, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr248a, htr345a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hc012yz, hc478yz, htr027a, htr123a, htr127b, htr178a, htr234a, htr348a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc468yz, hd12b, hd46a, htr123a, htr167a, htr168a, htr234a, htr348a, htr467a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr023a, htr027a, htr123a, htr267b, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr026a, htr027a, htr267b])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr023a, htr026c, htr067a, htr123a, htr467a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr067a, htr068a, htr678b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr267a, htr268a, htr678b])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc146zy, htr027a, htr028a, htr168a, htr247b, htr268c, htr467b])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, htr236b, htr267a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr467a, htr468a, htr678b])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12b, hd46a, htr123a, htr234a, htr347a, htr467a, htr478a, htr678a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, htr156c, htr168a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        linarith only [hlam, hc125yx, hc478yz, htr123a, htr157a, htr234a, htr348a, htr578a]
      ·
        linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a]
  ·
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc045zy, hd12b, hd78a, htr056a, htr123a, htr234a, htr345a, htr567a, htr678a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc145zy, hd12b, hd78a, htr123a, htr156a, htr234a, htr345a, htr567a, htr678a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc127yx, hd45a, hd56b, htr123a, htr178a, htr234a, htr345a, htr567a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr125b, htr156a, htr256a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, htr567a, htr568a, htr678c])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, htr567b, htr578a, htr678a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, hc456xy, htr123b, htr136a, htr234a, htr345a, htr346c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hc456xy, htr234a, htr236a, htr345a, htr346c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr246a, htr345a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hc012yz, hc456xy, htr024a, htr123a, htr234a, htr246a, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr023a, htr023b, htr023c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
      obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc456xy, htr023a, htr025a, htr234a, htr245c, htr246a, htr345a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr023a, htr026a, htr236c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr027a, htr127a, htr234a, htr345a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr028a, htr128a, htr234a, htr345a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, htr023b, htr034a, htr236a, htr346b])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr023b, htr036a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc027yx, hd45a, hd56b, htr023a, htr078a, htr234a, htr345a, htr567a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc456xy, htr245c, htr246a, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc456xy, htr245c, htr246a, htr258a, htr458a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hd45a, hd56b, htr023b, htr037a, htr234a, htr345a, htr367c, htr567a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr037c, htr038b, htr078c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc356yz, htr056a, htr057a, htr367a, htr567b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc356yz, htr156a, htr157a, htr367a, htr567b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hd45a, hd56b, htr234a, htr237a, htr345a, htr367c, htr567a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hd03b, hd45a, htr038a, htr234a, htr238a, htr345a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr126a, htr267a, htr345a, htr346b, htr367a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr246b, htr247c, htr267b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc356yz, htr237b, htr278a, htr367b, htr567a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a]
      ·
        linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a]
    ·
      have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr025a, htr025b, htr025c, _, _⟩
        linarith only [hlam, hc012yz, hc456yz, htr025a, htr123a, htr125b, htr156a, htr234a, htr346a])
      obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, htr025b, htr035c, htr235b])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hd12b, hd35a, htr034a, htr035a, htr123a, htr234a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr034a, htr036a, htr346c])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc456yz, htr034a, htr037a, htr346a, htr357c, htr567c])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc456yz, htr034a, htr038a, htr346a, htr358c, htr568c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, htr034b, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc456yz, hd12b, hd45a, htr056a, htr057a, htr123a, htr234a, htr346a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc456yz, hd12b, hd45a, htr056a, htr058a, htr123a, htr234a, htr346a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc456yz, hd07a, hd12b, htr078a, htr123a, htr234a, htr346a, htr567a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr123b, htr136a, htr234a, htr346c])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr124b, htr146a, htr234b, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc456yz, hd12b, hd45a, htr123a, htr156a, htr157a, htr234a, htr346a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc456yz, hd12b, hd45a, htr123a, htr156a, htr158a, htr234a, htr346a, htr458a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc126yx, hc456yz, htr123a, htr167a, htr234a, htr346a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr012a, htr014a, htr146c, htr167a, htr678a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc125yx, hc146zy, htr015a, htr016a, htr123a, htr234a, htr346a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, htr015a, htr017a, htr157b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr015a, htr018a, htr158b])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr023a, htr023b, htr023c, _, _⟩
        linarith only [hlam, hc012xy, hc456yz, htr015a, htr023a, htr156a, htr234a, htr346a])
      obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
      have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr024a, htr024b, htr024c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023a, htr024a, htr123a, htr234b, htr345a])
      obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc457xy, htr024a, htr025a, htr124b, htr147a, htr235b, htr345b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc478zy, htr146c, htr148a, htr167a, htr678a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr167a, htr168a, htr678c])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, htr234a, htr236a, htr346c])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, htr023c, htr037a, htr237a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr023c, htr038a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hc012yz, htr024a, htr123a, htr234a, htr246a, htr346a])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc457xy, htr024a, htr025a, htr235b, htr247a, htr345b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr045a, htr047a, htr123a, htr234c, htr247a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047c, htr048b, htr078c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, htr024c, htr048a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc125yx, htr023a, htr025a, htr123a, htr157a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc125yx, htr023a, htr025a, htr123a, htr158a, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc237yx, hc456yz, htr234a, htr278a, htr346a, htr567a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr023a, htr027a, htr123a, htr278a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc012yz, hc456yz, htr027a, htr123a, htr234a, htr267c, htr346a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, htr026a, htr027a, htr267c])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc012yz, htr026b, htr067a, htr126a, htr267a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr067a, htr068a, htr678c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr267a, htr268a, htr678c])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr123a, htr234c, htr247a, htr345a, htr347a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr023c, htr034c, htr048a, htr123a, htr345a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr123a, htr234a, htr346c, htr367a, htr678a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr367a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hd12b, hd36a, htr023a, htr028a, htr123a, htr268b, htr368a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd12b, hd37a, htr126a, htr267a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr346b, htr367a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr346b, htr368a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        linarith only [hlam, hd12b, hd47a, htr126a, htr267a, htr478a, htr678a]
      ·
        linarith only [hlam, hd12b, hd78a, htr123a, htr234a, htr347a, htr478a]

theorem shard_133 {lam p : ℝ} (m : NineModel lam p)
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
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr458a : m.d 4 5 + lam ≤ m.d 5 8)
    (htr458b : m.d 4 5 < m.d 4 8)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr358a : m.d 3 5 + lam ≤ m.d 5 8)
    (htr358b : m.d 3 5 < m.d 3 8)
    (htr358c : m.d 3 8 < m.d 5 8)
    (htr567a : m.d 6 7 + lam ≤ m.d 5 6)
    (htr567b : m.d 6 7 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 5 6)
    : False :=
  proof_shard_133 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr013a htr013b htr013c htr045a htr045b htr045c htr125a htr125b htr125c htr126a htr126b htr126c htr127a htr127b htr127c htr128a htr128b htr128c htr135a htr135b htr135c htr145a htr145b htr145c htr235a htr235b htr235c htr245a htr245b htr245c htr456a htr456b htr456c htr356a htr356b htr356c htr457a htr457b htr457c htr357a htr357b htr357c htr458a htr458b htr458c htr358a htr358b htr358c htr567a htr567b htr567c

#print axioms shard_133
end Jsp404.NoSatNineDBMTerminal
