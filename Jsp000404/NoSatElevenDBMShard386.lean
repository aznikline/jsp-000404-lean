import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_386 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
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
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, htr012c, htr016b, htr026c])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr013c, htr016b, htr036c])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr014c, htr016b, htr046c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr015c, htr016b, htr056c])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, htr012b, htr026a, htr126a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced123 := (m.htr 1 2 3 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr123a, htr123b, htr123c, _, _⟩
    linarith only [hlam, hc236xy, htr012a, htr016a, htr123a, htr126c])
  obtain ⟨htr123a, htr123b, htr123c, _, _⟩ := hforced123
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, htr013b, htr036a, htr136a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc346xy, htr013a, htr016a, htr134a, htr136c])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc356xy, htr013a, htr016a, htr135a, htr136c])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr014b, htr046a, htr146a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc456xy, htr014a, htr016a, htr145a, htr146c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr015b, htr056a, htr156a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc567yx, htr015a, htr016a, htr156c, htr157a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc568yx, htr015a, htr016a, htr156c, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, hc569yx, htr015a, htr016a, htr156c, htr159a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, hc5610yx, htr015a, htr016a, htr1510a, htr156c])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc123yz, htr013a, htr016a, htr136c, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc134yz, htr014a, htr016a, htr146c, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc135yz, htr015a, htr016a, htr156c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc145yz, htr015a, htr016a, htr156c, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 2 3 4 (by decide) (by decide) with
    ⟨htr234a, htr234b, htr234c, _, _⟩ | ⟨htr234a, htr234b, htr234c, _, _⟩
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13a, hd46b, htr135a, htr234a, htr235a, htr346a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hd12a, hd56b, htr123a, htr234a, htr345a, htr456a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr157a, htr345a, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd14a, hd56b, htr145a, htr356a, htr357a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr158a, htr345a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd14a, hd56b, htr145a, htr356a, htr358a, htr458a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr159a, htr345a, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hd14a, hd56b, htr145a, htr356a, htr359a, htr459a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
      linarith only [hlam, hc134yz, htr145b, htr1510a, htr345a, htr4510a])
    obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
    have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
      linarith only [hlam, hd14a, hd56b, htr145a, htr3510a, htr356a, htr4510a])
    obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr123a, htr234a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr123a, htr234a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd12a, hd69b, htr123a, htr234a, htr346a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr169a, htr469a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd12a, hd78b, htr123a, htr235a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr123a, htr235a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd12a, hd89b, htr123a, htr235a, htr358a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd12a, hd910b, htr123a, htr235a, htr359a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        linarith only [hlam, hc126xy, hc5910zy, htr123a, htr168a, htr235a, htr3510a, htr689a, htr8910a])
      obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc126xy, hc589zy, htr123a, htr169a, htr235a, htr359a, htr6910a, htr8910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc126xy, hc579zy, htr016a, htr017a, htr123a, htr167b, htr235a, htr359a, htr679a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        rcases m.htr 1 7 8 (by decide) (by decide) with
          ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr178a, htr578a]
        ·
          linarith only [hlam, hc127xy, hc579zy, htr123a, htr178a, htr235a, htr359a, htr678a, htr679a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc126xy, hc578zy, htr016a, htr017a, htr123a, htr167b, htr235a, htr358a, htr678a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr179a, htr579a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc127xy, hc578zy, htr123a, htr179a, htr235a, htr358a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc126xy, hc589zy, htr123a, htr167a, htr235a, htr359a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc126xy, hc5910zy, htr123a, htr167a, htr235a, htr3510a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr134a, htr234a, htr235a, htr356a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hc123yz, htr134b, htr145a, htr234a, htr345a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr157a, htr235a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr158a, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr159a, htr235a, htr359a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr1510a, htr235a, htr3510a])
    obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr134a, htr234a, htr236a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd12a, hd36b, htr012a, htr016a, htr167a, htr367a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr134a, htr234a, htr236a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd12a, hd36b, htr012a, htr016a, htr168a, htr368a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hd13a, hd69b, htr134a, htr234a, htr236a, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hd12a, hd36b, htr012a, htr016a, htr169a, htr369a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr135a, htr357a, htr456a, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr135a, htr358a, htr456a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr135a, htr359a, htr456a, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr135a, htr3510a, htr4510a, htr456a])
    obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr134a, htr345a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd13a, hd79b, htr134a, htr345a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd13a, hd89b, htr134a, htr345a, htr458a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd13a, hd910b, htr134a, htr345a, htr459a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        linarith only [hlam, hc136xy, hc5910zy, htr134a, htr168a, htr345a, htr4510a, htr689a, htr8910a])
      obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc136xy, hc589zy, htr134a, htr169a, htr345a, htr459a, htr6910a, htr8910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc136xy, hc579zy, htr016a, htr017a, htr134a, htr167b, htr345a, htr459a, htr679a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        rcases m.htr 1 7 8 (by decide) (by decide) with
          ⟨htr178a, htr178b, htr178c, _, _⟩ | ⟨htr178a, htr178b, htr178c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr178a, htr578a]
        ·
          linarith only [hlam, hc137xy, hc579zy, htr134a, htr178a, htr345a, htr459a, htr678a, htr679a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc136xy, hc578zy, htr016a, htr017a, htr134a, htr167b, htr345a, htr458a, htr678a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr179a, htr579a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc137xy, hc578zy, htr134a, htr179a, htr345a, htr458a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc136xy, hc589zy, htr134a, htr167a, htr345a, htr459a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc136xy, hc5910zy, htr134a, htr167a, htr345a, htr4510a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]

theorem shard_386 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    : False :=
  proof_shard_386 m htr012a htr012b htr012c htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b

#print axioms shard_386
end Jsp404.NoSatElevenDBMTerminal
