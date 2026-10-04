import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_162 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr257b : m.d 5 7 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < (7/2 : ℝ)*lam := by
    linarith only [hd01braw, hp]
  have hd07a := (m.hrange 0 7 (by decide)).1
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < (7/2 : ℝ)*lam := by
    linarith only [hd14braw, hp]
  have hd17a := (m.hrange 1 7 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
  have hd28a := (m.hrange 2 8 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < (7/2 : ℝ)*lam := by
    linarith only [hd67braw, hp]
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, htr023a, htr024a, htr234b])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, htr023a, htr025a, htr235b])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, htr023c, htr034a, htr235a, htr345c])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr023c, htr035a, htr235a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  rcases m.htr 2 4 5 (by decide) (by decide) with
    ⟨htr245a, htr245b, htr245c, _, _⟩ | ⟨htr245a, htr245b, htr245c, _, _⟩
  ·
    have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr014a, htr014b, htr014c, _, _⟩
      linarith only [hlam, hd12a, hd34b, htr012a, htr014a, htr124c, htr245a, htr345a])
    obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
    have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr015a, htr015b, htr015c, _, _⟩
      linarith only [hlam, hc134yz, htr014a, htr015a, htr125c, htr245c, htr345a])
    obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc126xy, hc134yz, htr014a, htr016a, htr123a, htr234b, htr245a, htr345a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc127xy, hc134yz, htr014a, htr017a, htr123a, htr234b, htr245a, htr345a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr018a, htr018b, htr018c, _, _⟩
      linarith only [hlam, hc128xy, hc134yz, htr014a, htr018a, htr123a, htr234b, htr245a, htr345a])
    obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hd26a, hd34b, htr023a, htr026a, htr234b, htr245a, htr345a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hd27a, hd34b, htr023a, htr027a, htr234b, htr245a, htr345a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hd28a, hd34b, htr023a, htr028a, htr234b, htr245a, htr345a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc346yx, htr023c, htr036a, htr234b, htr245a, htr345a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc347yx, htr023c, htr037a, htr234b, htr245a, htr345a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc348yx, htr023c, htr038a, htr234b, htr245a, htr345a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, htr024c, htr045a, htr245a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc034yz, htr045b, htr056a, htr345a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc034yz, htr045b, htr057a, htr345a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
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
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013b, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr013b, htr038a, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr124c, htr145a, htr245a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr156a, htr345a, htr456a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr157a, htr345a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc012yx, hd34b, hd56a, htr016a, htr023a, htr167a, htr234b, htr245a, htr345a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc012yx, hd34b, hd56a, htr016a, htr023a, htr168a, htr234b, htr245a, htr345a, htr568a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hc346yx, htr234b, htr236a, htr245a, htr345a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hc347yx, htr234b, htr237a, htr245a, htr345a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, hc348yx, htr234b, htr238a, htr245a, htr345a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc012yx, hc567yz, htr015a, htr027a, htr157a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, htr257c, htr258b, htr278c])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc034yz, htr045b, htr058a, htr245c, htr258a, htr345a])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr158a, htr245c, htr258a, htr345a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hc012yx, hc458zy, htr015a, htr023a, htr158a, htr234b, htr245a, htr345a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc012yx, htr015a, htr023a, htr158a, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc012yx, hc567yz, htr015a, htr023a, htr157a, htr236a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc356zy, htr057b, htr078a, htr367a, htr567b, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc356zy, htr157b, htr178a, htr367a, htr567b, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc012yx, hc356zy, htr015a, htr026a, htr156a, htr267a, htr367a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr168a, htr245c, htr256c, htr267a, htr345a, htr678c])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014b, htr046a, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hd34b, hd56a, htr024c, htr046c, htr067a, htr245a, htr345a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc356zy, htr067a, htr068a, htr367a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 2 4 6 (by decide) (by decide) with
      ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
    ·
      linarith only [hlam, htr124c, htr146a, htr246a]
    ·
      linarith only [hlam, hd34b, hd56a, htr245a, htr246c, htr267a, htr345a, htr567a]
  ·
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, htr245a, htr246a, htr456c])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr245a, htr247a, htr457c])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 4 6 7 (by decide) (by decide) with
      ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
    ·
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
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc567yz, htr257a, htr258a, htr578c, htr678a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr245c, htr248b, htr258c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc567yz, htr267a, htr268a, htr578a, htr678b])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr234c, htr248a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr235c, htr258a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc567yz, htr367a, htr368a, htr578a, htr678b])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hc567yz, htr457a, htr458a, htr578c, htr678a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr246b, htr268a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        rcases m.htr 0 1 4 (by decide) (by decide) with
          ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
        ·
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, hc246yx, htr013a, htr014a, htr123b, htr124c, htr126a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hd12a, hd34b, htr023a, htr026a, htr126a, htr234a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr026a, htr027a, htr267b])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, htr026a, htr028a, htr268b])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, htr126a, htr127a, htr267b])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr126a, htr128a, htr268b])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc346yx, htr013a, htr014a, htr124c, htr136a, htr234c])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc134xy, htr013c, htr014a, htr036a, htr136a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr036a, htr037a, htr367b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr036a, htr038a, htr368b])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, htr136a, htr137a, htr367b])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr136a, htr138a, htr368b])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hd12a, hd34b, htr012a, htr014a, htr145a, htr345a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc124xy, hc567yz, htr014a, htr015a, htr126a, htr145b, htr267a, htr457a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc124xy, hc567yz, htr012a, htr016a, htr145a, htr167a, htr457a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a])
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
            linarith only [hlam, htr045a, htr048a, htr458c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr045b, htr057a, htr458a, htr578b])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr045b, htr058a, htr458a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, htr145a, htr146a, htr456c])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr145a, htr148a, htr458c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr015a, htr145a, htr157a, htr458a, htr578b])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr015a, htr145a, htr158a, htr458a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, hc124xy, hc567yz, htr123a, htr145a, htr236a, htr367a, htr457a])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc134xy, hc357zy, htr136a, htr145a, htr236a, htr237a, htr457a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd12a, hd34b, htr012a, htr017a, htr137c, htr234a, htr237a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hd34b, hd57a, htr037c, htr078a, htr234a, htr237a, htr578a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr017b, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc167yz, htr017a, htr018a, htr178c, htr678a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc134xy, hc567yz, htr136a, htr145a, htr236a, htr238a, htr368c, htr457a, htr678c])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc124xy, hc567yz, htr126a, htr145a, htr267b, htr278a, htr457a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a]
          ·
            linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a]
        ·
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc134yz, hc567yz, htr014a, htr016a, htr167a, htr345a, htr457a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          rcases m.htr 2 3 6 (by decide) (by decide) with
            ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
          ·
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, htr023a, htr026a, htr236b])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, htr023a, htr027a, htr236b, htr267b])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, htr023a, htr028a, htr236b, htr268b])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, htr023c, htr036a, htr236a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, htr023c, htr037a, htr236a, htr367b])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, htr023c, htr038a, htr236a, htr368b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc024xy, hc567yz, htr023a, htr045a, htr236a, htr367a, htr457a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hc467yz, hd12a, hd34b, htr045a, htr047a, htr123a, htr236a, htr345a, htr367a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, hc468yz, hd12a, hd34b, htr045a, htr048a, htr123a, htr236a, htr345a, htr368a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc034yz, htr045b, htr056a, htr345a, htr456a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc034yz, htr045b, htr057a, htr345a, htr457a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc567yz, hd12a, hd34b, htr057a, htr058a, htr123a, htr236a, htr345a, htr367a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc027xy, hc567yz, htr023a, htr078a, htr236a, htr367a, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, hc134yz, hc567yz, htr014a, htr017b, htr078a, htr345a, htr457a, htr678a])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc125xy, hc167yz, htr015a, htr017a, htr123a, htr236a, htr367a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, hc128xy, hc167yz, htr017a, htr018a, htr123a, htr236a, htr367a])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, htr012b, htr023a, htr126a, htr236b])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr136a, htr136b, htr136c, _, _⟩
              linarith only [hlam, htr123c, htr136a, htr236a])
            obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
            have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr145a, htr145b, htr145c, _, _⟩
              linarith only [hlam, htr014b, htr045a, htr145a])
            obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, htr014b, htr047a, htr147a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr148a, htr148b, htr148c, _, _⟩
              linarith only [hlam, htr014b, htr048a, htr148a])
            obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc134yz, htr145b, htr156a, htr345a, htr456a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            rcases m.htr 1 5 7 (by decide) (by decide) with
              ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
            ·
              linarith only [hlam, hc134yz, htr145b, htr157a, htr345a, htr457a]
            ·
              linarith only [hlam, hc012yx, hc567yz, htr015a, htr023a, htr157a, htr236a, htr367a]
          ·
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc346yx, htr023a, htr026a, htr234a, htr236b])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr027a, htr027b, htr027c, _, _⟩
              linarith only [hlam, htr026a, htr027a, htr267b])
            obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
            have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr028a, htr028b, htr028c, _, _⟩
              linarith only [hlam, htr026a, htr028a, htr268b])
            obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc034yz, htr046a, htr234a, htr236a, htr346b])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc035yz, htr056a, htr235a, htr236a, htr346b, htr456b])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hd34b, hd56a, htr056a, htr057a, htr345a, htr457a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hd34b, hd56a, htr056a, htr058a, htr345a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr126a, htr126b, htr126c, _, _⟩
              linarith only [hlam, htr012b, htr026a, htr126a])
            obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, htr012b, htr026a, htr127a, htr267b])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr128a, htr128b, htr128c, _, _⟩
              linarith only [hlam, htr012b, htr026a, htr128a, htr268b])
            obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
            have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr145a, htr145b, htr145c, _, _⟩
              linarith only [hlam, hc012yx, hc567yz, htr014a, htr026a, htr145a, htr267a, htr457a])
            obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
            have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr015a, htr015b, htr015c, _, _⟩
              linarith only [hlam, hc134yz, htr014a, htr015a, htr145c, htr345a])
            obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
            have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr017a, htr017b, htr017c, _, _⟩
              linarith only [hlam, htr015c, htr017b, htr057c])
            obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
            have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr018a, htr018b, htr018c, _, _⟩
              linarith only [hlam, htr015c, htr018b, htr058c])
            obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
            have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr136a, htr136b, htr136c, _, _⟩
              linarith only [hlam, hc346yx, htr134b, htr136a, htr145a, htr345a])
            obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, htr136a, htr137a, htr367b])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr138a, htr138b, htr138c, _, _⟩
              linarith only [hlam, htr136a, htr138a, htr368b])
            obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hc134yz, htr146a, htr234a, htr236a, htr346b])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr157a, htr157b, htr157c, _, _⟩
              linarith only [hlam, hc134yz, htr145b, htr157a, htr345a, htr457a])
            obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, hc134yz, htr145b, htr158a, htr345a, htr458a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc012yx, hc567yz, htr017a, htr026a, htr178a, htr267a, htr578a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc012yx, hc567yz, htr015a, htr026a, htr157a, htr267b, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hd46a, hd67b, htr046a, htr047a, htr478a, htr678a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hc467yz, htr047a, htr048a, htr478c, htr678a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd46a, hd67b, htr146a, htr147a, htr478a, htr678a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc024xy, hc467yz, htr026a, htr045a, htr145a, htr147a, htr267a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc346yx, htr034b, htr036a, htr045a, htr345a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, htr036a, htr037a, htr367b])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, htr036a, htr038a, htr368b])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hd34b, hd57a, htr045a, htr047c, htr078a, htr345a, htr578a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr148a, htr148b, htr148c, _, _⟩
                linarith only [hlam, hc134yz, htr045a, htr048a, htr148a, htr345a])
              obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
              have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr237a, htr237b, htr237c, _, _⟩
                linarith only [hlam, hc346yx, hc347zy, htr145a, htr147a, htr236a, htr237a, htr345a])
              obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
              have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr238a, htr238b, htr238c, _, _⟩
                linarith only [hlam, hc567yz, htr237c, htr238a, htr278a, htr368c, htr578a, htr678c])
              obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
              rcases m.htr 3 7 8 (by decide) (by decide) with
                ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
              ·
                linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a]
              ·
                linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a]
            ·
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd34b, hd57a, htr023c, htr037a, htr234a, htr347b, htr478a, htr578a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc346yx, hc357zy, htr036a, htr037a, htr345a, htr457c, htr478a, htr578a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, htr036a, htr038a, htr368b])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc024xy, hc567yz, htr026a, htr045a, htr267a, htr457c, htr478a, htr578a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hd34b, hd57a, htr045a, htr047a, htr345a, htr478a, htr578a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hd34b, hd57a, htr045a, htr048a, htr345a, htr478b, htr578a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc034yz, htr047b, htr078a, htr345a, htr457c, htr478a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              rcases m.htr 1 4 7 (by decide) (by decide) with
                ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
              ·
                linarith only [hlam, hc134yz, htr147b, htr178a, htr345a, htr457c, htr478a]
              ·
                linarith only [hlam, htr014b, htr047a, htr147a]
      ·
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc246yx, hd34b, hd78a, htr023a, htr026a, htr234a, htr245a, htr457a, htr578a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hd34b, hd78a, htr023a, htr027a, htr234a, htr257b, htr578a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, hc248yx, hd34b, hd78a, htr023a, htr028a, htr234a, htr245a, htr457a, htr578a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hd07a, hd34b, htr078a, htr345a, htr457a, htr578a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
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
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hd17a, hd34b, htr178a, htr345a, htr457a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc478zy, htr245a, htr248a, htr457a, htr578a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr245b, htr258a, htr457a, htr578c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr257b, htr278a, htr578a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr234c, htr248a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr345b, htr358a, htr457a, htr578c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, htr347b, htr378a, htr457b, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr457a, htr458a, htr578c])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, htr457b, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        rcases m.htr 0 1 4 (by decide) (by decide) with
          ⟨htr014a, htr014b, htr014c, _, _⟩ | ⟨htr014a, htr014b, htr014c, _, _⟩
        ·
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc346yx, htr013a, htr014a, htr124c, htr136a, htr234c])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc134xy, htr013c, htr014a, htr036a, htr136a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc347yx, htr013a, htr014a, htr124c, htr137a, htr234c])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc134xy, htr013c, htr014a, htr037a, htr137a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc348yx, htr013a, htr014a, htr124c, htr138a, htr234c])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc134xy, htr013c, htr014a, htr038a, htr138a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hd12a, hd34b, htr012a, htr014a, htr145a, htr345a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hd14b, hd78a, htr014a, htr015a, htr145b, htr457a, htr578a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc124xy, hc178zy, htr012a, htr018a, htr145a, htr457a, htr578a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr014b, htr045a, htr145a])
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
            linarith only [hlam, htr045a, htr048a, htr458c])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, htr045b, htr056a, htr457a, htr567b])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, htr045b, htr057a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, htr145a, htr146a, htr456c])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, htr145a, htr147a, htr457c])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr145a, htr148a, htr458c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, htr015a, htr018a, htr148b, htr156a, htr458b, htr568b])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr015a, htr145a, htr157a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, hc134xy, hd34b, hd78a, htr136a, htr145a, htr234a, htr236a, htr457a, htr578a])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc124xy, hc356zy, htr014a, htr018a, htr123a, htr168b, htr236a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr016a, htr018a, htr168b])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc146yx, htr014a, htr016c, htr067a, htr168a, htr678c])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc146yx, htr014a, htr016c, htr068a, htr168a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr167a, htr168a, htr678c])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc134xy, hd34b, hd78a, htr137a, htr145a, htr234a, htr237a, htr457a, htr578a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          rcases m.htr 2 3 8 (by decide) (by decide) with
            ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
          ·
            linarith only [hlam, hc124xy, hc378zy, htr123a, htr145a, htr238a, htr457a, htr578a]
          ·
            linarith only [hlam, hc134xy, hd34b, hd78a, htr138a, htr145a, htr234a, htr238a, htr457a, htr578a]
        ·
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc134yz, hc178zy, htr014a, htr018a, htr345a, htr457a, htr578a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hd01b, hd78a, htr014a, htr145a, htr457a, htr578a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc134yz, htr014a, htr015a, htr145c, htr345a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc134yz, htr015b, htr056a, htr145b, htr345a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, htr015c, htr016b, htr056c])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc134yz, htr015b, htr057a, htr145b, htr345a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, htr015c, htr017b, htr057c])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr057a, htr058a, htr578c])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, hc346yx, htr134b, htr136a, htr145a, htr345a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc347yx, htr134b, htr137a, htr145a, htr345a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc348yx, htr134b, htr138a, htr145a, htr345a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34b, hd78a, htr145a, htr147a, htr345a, htr457b, htr578a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc134yz, htr023c, htr037a, htr147a, htr234a, htr347b])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc134yz, htr145b, htr156a, htr345a, htr456a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc134yz, htr145b, htr157a, htr345a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr157a, htr158a, htr578c])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc134yz, htr145c, htr147a, htr156c, htr167a, htr345a, htr467c])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc134yz, htr147a, htr234a, htr237a, htr347b])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc012yx, hc378zy, htr015a, htr023a, htr157a, htr238a, htr578a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc013yx, hd34b, hd78a, htr015a, htr038a, htr157a, htr234a, htr238a, htr578a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc348yx, htr034b, htr038a, htr045a, htr345a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, htr045a, htr046a, htr456c])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, htr045a, htr047a, htr457c])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc134yz, htr148a, htr234a, htr238a, htr348b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc348yx, hc356zy, htr036a, htr038a, htr145a, htr148a, htr345a, htr458b, htr568b])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc056zy, htr067a, htr147a, htr148a, htr458b, htr467c, htr568b])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc134yz, htr023c, htr036a, htr146a, htr234a, htr346b])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hd34b, hd56a, htr023c, htr036a, htr136c, htr168a, htr234a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr236a, htr236b, htr236c, _, _⟩
            linarith only [hlam, htr023c, htr036a, htr236a])
          obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc256zy, htr147a, htr148a, htr267a, htr458b, htr467c, htr568b])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc012yx, hc678zy, htr015a, htr026a, htr157a, htr268a, htr578a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, hc346yx, htr036b, htr068a, htr234a, htr236c, htr268a])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd34b, hd56a, htr023c, htr036a, htr234a, htr267a, htr268a, htr367a, htr568a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            linarith only [hlam, hc346yx, htr234a, htr236c, htr268a, htr368a]
          ·
            linarith only [hlam, hd34b, hd56a, htr023c, htr036a, htr234a, htr368a, htr568a]
    ·
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr023a, htr026a, htr234a, htr246b, htr467a, htr567a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr023a, htr027a, htr234a, htr247b, htr467b, htr567a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc248yx, hd34b, hd56a, htr023a, htr028a, htr234a, htr245a, htr456c, htr467a, htr567a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr023c, htr036a, htr234a, htr346b, htr467a, htr567a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc356zy, htr036a, htr037a, htr347b, htr467b, htr567a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc348yx, hc356zy, htr036a, htr038a, htr345a, htr456c, htr467a, htr567a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr568a, htr678c])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr056a, htr057a, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc456zy, htr056a, htr058a, htr467a, htr568c, htr678c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd07a, hd34b, htr078a, htr345a, htr456c, htr467a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
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
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr013b, htr036a, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013b, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013b, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145yz, htr156a, htr456c, htr467a, htr568a, htr678c])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr156a, htr157a, htr345a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc456zy, htr156a, htr158a, htr467a, htr568c, htr678c])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd17a, hd34b, htr178a, htr345a, htr456c, htr467a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr346b, htr467a, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc024xy, hc356zy, htr023a, htr045a, htr236a, htr456c, htr467a, htr567a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr045a, htr046a, htr345a, htr467a, htr567a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr045a, htr047a, htr345a, htr467b, htr567a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc034yz, htr046b, htr067a, htr345a, htr456c, htr467a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr067a, htr068a, htr678c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hc124xy, hc356zy, htr123a, htr145a, htr236a, htr456c, htr467a, htr567a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd12a, hd34b, htr012a, htr014a, htr145a, htr345a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc134yz, htr014a, htr015a, htr145c, htr345a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, htr015a, htr017a, htr157c])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, htr015a, htr018a, htr158c])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr014b, htr047a, htr146a, htr467c])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014b, htr047a, htr147a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      rcases m.htr 1 6 7 (by decide) (by decide) with
        ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
      ·
        linarith only [hlam, hc134yz, htr146b, htr167a, htr345a, htr456c, htr467a]
      ·
        linarith only [hlam, hc012yx, hc356zy, htr015a, htr023a, htr156c, htr167a, htr236a, htr567a]

theorem shard_162 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr257b : m.d 5 7 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    : False :=
  proof_shard_162 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr013a htr013b htr013c htr235a htr235b htr235c htr125a htr125b htr125c htr135a htr135b htr135c htr256a htr256b htr256c htr457a htr457b htr457c htr257a htr257b htr257c htr347a htr347b htr347c htr357a htr357b htr357c htr568a htr568b htr568c htr023a htr023b htr023c

#print axioms shard_162
end Jsp404.NoSatNineDBMTerminal
