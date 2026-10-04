import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_110 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr578a : m.d 7 8 + lam ≤ m.d 5 7)
    (htr578b : m.d 7 8 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 5 7)
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
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr478a : m.d 7 8 + lam ≤ m.d 4 7)
    (htr478b : m.d 7 8 < m.d 4 8)
    (htr478c : m.d 4 8 < m.d 4 7)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < (7/2 : ℝ)*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < (7/2 : ℝ)*lam := by
    linarith only [hd26braw, hp]
  obtain ⟨hd27a, hd27braw⟩ := m.hrange 2 7 (by decide)
  have hd27b : m.d 2 7 < (7/2 : ℝ)*lam := by
    linarith only [hd27braw, hp]
  obtain ⟨hd28a, hd28braw⟩ := m.hrange 2 8 (by decide)
  have hd28b : m.d 2 8 < (7/2 : ℝ)*lam := by
    linarith only [hd28braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < (7/2 : ℝ)*lam := by
    linarith only [hd46braw, hp]
  have hd48a := (m.hrange 4 8 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < (7/2 : ℝ)*lam := by
    linarith only [hd56braw, hp]
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
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
      linarith only [hlam, htr245a, htr247a, htr457b])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 4 6 7 (by decide) (by decide) with
      ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
    ·
      have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr026a, htr026b, htr026c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr023a, htr026a, htr234a, htr246c, htr467a, htr567a])
      obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr023a, htr027a, htr234a, htr247c, htr467c, htr567a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, hc248xy, hd34a, hd56b, htr023a, htr028a, htr234a, htr245a, htr456b, htr467a, htr567a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr023b, htr036a, htr234a, htr346c, htr467a, htr567a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc356yz, htr036a, htr037a, htr347c, htr467c, htr567a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc348xy, hc356yz, htr036a, htr038a, htr345a, htr456b, htr467a, htr567a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr567a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr056a, htr057a, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr126a, htr126b, htr126c, _, _⟩
        linarith only [hlam, htr012c, htr026a, htr126a])
      obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, htr012c, htr027a, htr127a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, htr012c, htr028a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr136a, htr136b, htr136c, _, _⟩
        linarith only [hlam, htr013c, htr036a, htr136a])
      obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr138a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr156a, htr157a, htr345a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr236a, htr236b, htr236c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr346c, htr467a, htr567a])
      obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc024yx, hc356yz, htr023a, htr045a, htr236a, htr456b, htr467a, htr567a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr045a, htr046a, htr345a, htr467a, htr567a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr045a, htr047a, htr345a, htr467c, htr567a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047a, htr048a, htr478c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc034zy, htr046c, htr067a, htr345a, htr456b, htr467a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr047b, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr145a, htr145b, htr145c, _, _⟩
        linarith only [hlam, hc124yx, hc356yz, htr123a, htr145a, htr236a, htr456b, htr467a, htr567a])
      obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
      have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr014a, htr014b, htr014c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr145a, htr345a])
      obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
      have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr015a, htr015b, htr015c, _, _⟩
        linarith only [hlam, hc134zy, htr014a, htr015a, htr145b, htr345a])
      obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, htr015a, htr017a, htr157b])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc128yx, hc356yz, htr015a, htr018a, htr123a, htr156a, htr236a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, htr014c, htr047a, htr146a, htr467b])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014c, htr047a, htr147a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr047a, htr148a, htr478c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hd34a, hd56b, htr045b, htr058a, htr156a, htr158a, htr345a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 1 6 7 (by decide) (by decide) with
        ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
      ·
        linarith only [hlam, hc012xy, hc356yz, htr015a, htr023a, htr156b, htr167a, htr236a, htr567a]
      ·
        linarith only [hlam, hc134zy, htr146c, htr167a, htr345a, htr456b, htr467a]
    ·
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr467a, htr468a, htr678c])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
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
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc035zy, htr056a, htr235a, htr236a, htr346c, htr456c])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr056a, htr057a, htr345a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr012c, htr026a, htr126a])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc134zy, htr146a, htr234a, htr236a, htr346c])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc135zy, htr156a, htr235a, htr236a, htr346c, htr456c])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr156a, htr157a, htr345a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc468yx, htr235a, htr236a, htr345b, htr346c, htr348a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr245a, htr248a, htr348a, htr456a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc568yx, htr235a, htr236a, htr346c, htr358a, htr456c])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc356xy, htr235c, htr236a, htr258a, htr358a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc278zy, hc346xy, htr023a, htr028a, htr234a, htr367a, htr678a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc346xy, htr026b, htr067a, htr234a, htr236b, htr367a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, htr026c, htr027b, htr067c])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr067b, htr078a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, htr012c, htr027a, htr127a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr012c, htr028a, htr128a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr016c, htr067a, htr167a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd46b, hd78a, htr014a, htr017a, htr146a, htr167b, htr678a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr016c, htr067a, htr168a, htr678c])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr167b, htr178a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc125yx, hd46b, hd78a, htr012c, htr014a, htr015a, htr026a, htr146a, htr267a, htr678a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc128yx, hd46b, hd78a, htr012c, htr014a, htr018a, htr026a, htr146a, htr267a, htr678a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc012xy, hc378zy, htr013a, htr026a, htr138a, htr267a, htr678a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc012xy, hd56b, hd78a, htr014a, htr026a, htr145a, htr267a, htr456a, htr678a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc024yx, hd46b, hd78a, htr026a, htr045a, htr145a, htr146a, htr267a, htr678a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc346xy, htr034c, htr036a, htr045a, htr345a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, htr036a, htr037a, htr367c])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc348xy, htr036a, htr038a, htr234a, htr236a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc346xy, hc478zy, htr045a, htr048a, htr345a, htr367a, htr678a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr013c, htr036a, htr136a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr014c, htr048a, htr148a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc012xy, hc578zy, htr015a, htr026a, htr158a, htr267a, htr678a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr045b, htr058a, htr156a, htr158a, htr345a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hd03b, hd78a, htr036a, htr236a, htr237a, htr367b, htr678a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc034zy, htr047a, htr234a, htr237a, htr347c])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc134zy, htr045a, htr047a, htr147a, htr345a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc034zy, htr048a, htr234a, htr238a, htr348c])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, htr267a, htr268a, htr678c])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, htr367a, htr368a, htr678c])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd56b, htr156a, htr158a, htr345a, htr458a]
          ·
            linarith only [hlam, hc568yx, htr145a, htr146a, htr456c, htr458a]
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, htr023a, htr026a, htr236c])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr027a, htr027b, htr027c, _, _⟩
            linarith only [hlam, hc356yz, htr023a, htr027a, htr236a, htr257c, htr567c])
          obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
          have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr028a, htr028b, htr028c, _, _⟩
            linarith only [hlam, hc278zy, hc356yz, htr023a, htr028a, htr236a, htr567a, htr678a])
          obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, htr023b, htr036a, htr236a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc027yx, hc356yz, htr023a, htr078a, htr236a, htr567a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr126a, htr126b, htr126c, _, _⟩
            linarith only [hlam, htr012c, htr023a, htr126a, htr236c])
          obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, htr012c, htr027a, htr127a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr128a, htr128b, htr128c, _, _⟩
            linarith only [hlam, htr012c, htr028a, htr128a])
          obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
          have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr136a, htr136b, htr136c, _, _⟩
            linarith only [hlam, htr123b, htr136a, htr236a])
          obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
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
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc134zy, htr015c, htr057a, htr145c, htr345a, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, htr015b, htr017c, htr057b])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc347xy, htr134c, htr137a, htr145a, htr345a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc348xy, htr134c, htr138a, htr145a, htr345a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc128yx, hc356yz, htr015a, htr018a, htr123a, htr156a, htr236a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc134zy, htr145c, htr157a, htr345a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc012xy, hc356yz, htr016a, htr023a, htr167a, htr236a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr167a, htr168a, htr678c])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr017c, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc012xy, hc568yx, htr015a, htr023a, htr156a, htr235a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc134zy, htr145a, htr245c, htr258a, htr345b, htr358a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, htr245b, htr248c, htr258b])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, htr234b, htr248a, htr348a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc356yz, htr023b, htr037a, htr236a, htr367c, htr567a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr037c, htr038b, htr078c])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc034zy, htr046a, htr346b, htr367a, htr467a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc346yz, htr046a, htr047a, htr367a, htr467b])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc134zy, htr146a, htr346b, htr367a, htr467a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc024yx, hc346yz, htr023a, htr045a, htr145a, htr146a, htr236a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr045a, htr046b, htr067a, htr345a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc134zy, htr045a, htr047a, htr147a, htr345a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc356yz, htr236a, htr237a, htr367c, htr567a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc013xy, hc356yz, htr015a, htr038a, htr156a, htr236a, htr238a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc012xy, hc356yz, htr015a, htr023a, htr156a, htr236c, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc356yz, htr237b, htr278a, htr367b, htr567a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc478zy, hd12b, hd34a, htr045a, htr048a, htr123a, htr237a, htr345a, htr378a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, htr014c, htr048a, htr148a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc012xy, hc578zy, htr015a, htr023a, htr158a, htr237a, htr378a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc134zy, htr045b, htr058a, htr145c, htr158a, htr345a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc246yz, htr046a, htr048a, htr268a, htr468b])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hc356yz, htr267a, htr268a, htr368a, htr567a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            linarith only [hlam, hc134zy, htr145c, htr158a, htr345a, htr458a]
          ·
            linarith only [hlam, hc134zy, htr145a, htr345b, htr358a, htr458a]
      ·
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr012a, htr014c, htr046a, htr467a, htr678a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr046c, htr056b, htr456c])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr056a, htr057a, htr345a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr126a, htr126b, htr126c, _, _⟩
          linarith only [hlam, hc246xy, htr013a, htr014a, htr123c, htr124b, htr126a])
        obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hd12b, hd34a, htr023a, htr026a, htr126a, htr234a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr127a, htr127b, htr127c, _, _⟩
          linarith only [hlam, hc247xy, htr013a, htr014a, htr123c, htr124b, htr127a])
        obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hd12b, hd34a, htr023a, htr027a, htr127a, htr234a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
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
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc347xy, htr013a, htr014a, htr124b, htr137a, htr234b])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc134yx, htr013b, htr014a, htr037a, htr137a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
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
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457b])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, htr014b, htr046a, htr146a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, htr145a, htr147a, htr457b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, htr145c, htr156a, htr457a, htr567c])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, htr145c, htr157a, htr457a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc124yx, hc568yx, htr123a, htr145a, htr235a, htr358a, htr456a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, htr345b, htr348c, htr358b])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr045a, htr048a, htr348a, htr456a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr014b, htr048a, htr148a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr024b, htr048a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
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
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr036b, htr067a, htr234a, htr236a, htr567a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr067a, htr068a, htr678c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr067b, htr078a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr158a, htr358a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc125yx, htr012a, htr015c, htr058a, htr158a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, htr016c, htr067a, htr167a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr016c, htr067a, htr168a, htr678c])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, htr167b, htr178a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc134yx, hc357yz, htr136a, htr145a, htr236a, htr237a, htr457a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hd12b, hd34a, htr012a, htr017a, htr137b, htr234a, htr237a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr125b, htr158a, htr258a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr234a, htr237b, htr278a, htr567a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc134yx, hc178zy, htr014a, htr018a, htr136a, htr367a, htr678a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hd12b, hd34a, htr012a, htr018a, htr138b, htr234a, htr238a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, htr267a, htr268a, htr678c])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, htr367a, htr368a, htr678c])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            linarith only [hlam, hc134yx, hc578zy, htr136a, htr145a, htr367a, htr458a, htr678a]
          ·
            linarith only [hlam, hc135yx, hd34a, hd56b, htr136a, htr158a, htr234a, htr236a, htr456a, htr458a]
        ·
          have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr015a, htr015b, htr015c, _, _⟩
            linarith only [hlam, hc124yx, hc356yz, htr014a, htr015a, htr123a, htr145c, htr236a, htr456a])
          obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc027yx, hc356yz, htr023a, htr078a, htr236a, htr567a, htr678a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr158a, htr358a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc125yx, htr012a, htr015c, htr058a, htr158a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc127yx, hc356yz, htr123a, htr178a, htr236a, htr567a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr237a, htr237b, htr237c, _, _⟩
            linarith only [hlam, hc134yx, hc356yz, htr137a, htr145a, htr236a, htr237a, htr456a])
          obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc134yx, hc356yz, htr138a, htr145a, htr236a, htr238a, htr456a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, htr125b, htr158a, htr258a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc124yx, hc356yz, htr126a, htr145a, htr267a, htr367a, htr456a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc356yz, htr237b, htr278a, htr367b, htr567a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc124yx, hc178zy, htr014a, htr018a, htr123a, htr237a, htr378a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            linarith only [hlam, hc124yx, hc578zy, htr123a, htr145a, htr237a, htr378a, htr458a]
          ·
            linarith only [hlam, hc125yx, hc356yz, htr123a, htr158a, htr236a, htr456a, htr458a]
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
      linarith only [hlam, hd26b, hd34a, htr023a, htr026a, htr234c, htr245a, htr345a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hd27b, hd34a, htr023a, htr027a, htr234c, htr245a, htr345a])
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
      linarith only [hlam, hc347xy, htr023b, htr037a, htr234c, htr245a, htr345a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc348xy, htr023b, htr038a, htr234c, htr245a, htr345a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr045a, htr045b, htr045c, _, _⟩
      linarith only [hlam, htr024b, htr045a, htr245a])
    obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc034zy, htr045c, htr056a, htr345a, htr456a])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc034zy, htr045c, htr057a, htr345a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr027b, htr078a, htr245b, htr257b, htr345a, htr567a, htr678a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr126a, htr126b, htr126c, _, _⟩
      linarith only [hlam, htr012c, htr026a, htr126a])
    obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, htr012c, htr027a, htr127a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr128a, htr128b, htr128c, _, _⟩
      linarith only [hlam, htr012c, htr028a, htr128a])
    obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr013c, htr036a, htr136a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr137a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, htr013c, htr038a, htr138a])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr145a, htr145b, htr145c, _, _⟩
      linarith only [hlam, htr124b, htr145a, htr245a])
    obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc134zy, htr145c, htr157a, htr345a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc012xy, hd34a, hd56b, htr016a, htr023a, htr167a, htr234c, htr245a, htr345a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr167a, htr168a, htr678c])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, htr017c, htr078a, htr178a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hc346xy, htr234c, htr236a, htr245a, htr345a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hc347xy, htr234c, htr237a, htr245a, htr345a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr238a, htr238b, htr238c, _, _⟩
      linarith only [hlam, hc348xy, htr234c, htr238a, htr245a, htr345a])
    obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr245b, htr257b, htr278a, htr345a, htr567a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hd12b, hd48a, htr123a, htr234c, htr245a, htr345a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc012xy, hc568yx, htr015a, htr023a, htr156a, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc012xy, hc356yz, htr015a, htr026a, htr156a, htr267a, htr367a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc134zy, htr146c, htr167a, htr245b, htr256b, htr267a, htr345a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014c, htr046a, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hd34a, hd56b, htr024b, htr046b, htr067a, htr245a, htr345a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr067a, htr068a, htr678c])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 2 4 6 (by decide) (by decide) with
      ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
    ·
      linarith only [hlam, hd34a, hd56b, htr245a, htr246b, htr267a, htr345a, htr567a]
    ·
      linarith only [hlam, htr124b, htr146a, htr246a]

theorem shard_110 {lam p : ℝ} (m : NineModel lam p)
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
    (htr678a : m.d 7 8 + lam ≤ m.d 6 7)
    (htr678b : m.d 7 8 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 6 7)
    (htr568a : m.d 6 8 + lam ≤ m.d 5 6)
    (htr568b : m.d 6 8 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 5 6)
    (htr578a : m.d 7 8 + lam ≤ m.d 5 7)
    (htr578b : m.d 7 8 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 5 7)
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
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr478a : m.d 7 8 + lam ≤ m.d 4 7)
    (htr478b : m.d 7 8 < m.d 4 8)
    (htr478c : m.d 4 8 < m.d 4 7)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr023c : m.d 0 3 < m.d 0 2)
    : False :=
  proof_shard_110 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr568a htr568b htr568c htr578a htr578b htr578c htr013a htr013b htr013c htr235a htr235b htr235c htr125a htr125b htr125c htr135a htr135b htr135c htr256a htr256b htr256c htr357a htr357b htr357c htr347a htr347b htr347c htr478a htr478b htr478c htr457a htr457b htr457c htr257a htr257b htr257c htr023a htr023b htr023c

#print axioms shard_110
end Jsp404.NoSatNineDBMTerminal
