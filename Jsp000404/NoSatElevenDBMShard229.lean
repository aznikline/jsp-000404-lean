import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_229 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc134zy, htr015c, htr056a, htr145c, htr345a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr245a, htr246a, htr456b])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr245c, htr256a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr234b, htr245a, htr346a, htr456b])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr345c, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  rcases m.htr 1 4 6 (by decide) (by decide) with
    ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014c, htr046a, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hc467yx, htr014c, htr045a, htr146a, htr245a, htr247a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567yx, htr014c, htr045a, htr146a, htr456c, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc134zy, htr145c, htr157a, htr345a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568yx, htr014c, htr045a, htr146a, htr456c, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc134zy, htr145c, htr158a, htr345a, htr458a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569yx, htr014c, htr045a, htr146a, htr456c, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr159a, htr159b, htr159c, _, _⟩
      linarith only [hlam, hc134zy, htr145c, htr159a, htr345a, htr459a])
    obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr145a, htr146a, htr345a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd34a, hd68b, htr145a, htr146a, htr345a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc456xy, htr045a, htr046b, htr068a, htr468a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 3 6 7 (by decide) (by decide) with
      ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc346yz, htr014c, htr047a, htr146a, htr367a, htr467b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd34a, hd78b, htr045a, htr047a, htr345a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd34a, hd79b, htr045a, htr047a, htr345a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hd34a, hd710b, htr045a, htr047a, htr345a, htr4710a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc346yz, htr367a, htr467c, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc346yz, htr367b, htr379a, htr467a, htr679a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hc346yz, htr367a, htr467c, htr4710a, htr6710a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, hc346yz, htr367b, htr3710a, htr467a, htr6710a])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hc012xy, hc7910yz, htr015a, htr023a, htr159a, htr237a, htr3710a, htr5910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd12b, hd910a, htr123a, htr237a, htr379a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
    ·
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr045a, htr047a, htr345a, htr457c, htr578a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc346yz, htr014c, htr048a, htr146a, htr368a, htr468b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd46b, hd67a, htr014c, htr047a, htr146a, htr479a, htr679a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr045a, htr048a, htr345a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd24a, hd78b, htr247a, htr479a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc346yz, htr368a, htr468c, htr489a, htr689a]
        ·
          linarith only [hlam, hc016xy, hc378yz, htr015a, htr068a, htr157a, htr389a, htr578a, htr689a]
      ·
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc012xy, hc567zy, htr017a, htr023a, htr178a, htr236a, htr367a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc567zy, htr367a, htr368a, htr578a, htr678c])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc567zy, htr458c, htr489a, htr578c, htr678a, htr789a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr045a, htr048a, htr345a, htr489a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc012xy, hc689yz, htr015a, htr023a, htr158a, htr236a, htr369a, htr589a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc167zy, htr179a, htr367a, htr369a, htr679c])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd24a, hd79b, htr178a, htr179a, htr247a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        rcases m.htr 1 4 7 (by decide) (by decide) with
          ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
        ·
          linarith only [hlam, hc467zy, htr014c, htr048a, htr147a, htr478b, htr678a]
        ·
          linarith only [hlam, hd46b, hd67a, htr146a, htr147a, htr478a, htr678a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc134zy, htr045a, htr046a, htr146a, htr345a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc134zy, htr015c, htr057a, htr145c, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc134zy, htr145c, htr157a, htr345a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr245a, htr247a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245c, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr234b, htr245a, htr347a, htr457b])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      rcases m.htr 1 4 7 (by decide) (by decide) with
        ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr014c, htr047a, htr147a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr046c, htr047b, htr067c])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, htr046b, htr067a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc678yx, htr014c, htr046a, htr147a, htr467c, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc679yx, htr014c, htr046a, htr147a, htr467c, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr145a, htr147a, htr345a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc457xy, htr045a, htr047b, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr145a, htr147a, htr345a, htr467c, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr468a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc012xy, hc678zy, htr015a, htr023a, htr156a, htr237a, htr378a, htr568a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc347yz, htr014c, htr048a, htr147a, htr378a, htr478b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr045a, htr048a, htr345a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr469a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc012xy, hc689zy, htr015a, htr023a, htr156a, htr238a, htr389a, htr569a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc347yz, htr378a, htr478c, htr489a, htr789a]
        ·
          linarith only [hlam, hc017xy, hc368yz, htr015a, htr078a, htr156a, htr389a, htr568a, htr789a]
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc134zy, htr045a, htr047a, htr147a, htr345a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc134zy, htr145c, htr158a, htr345a, htr458a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          rcases m.htr 1 4 8 (by decide) (by decide) with
            ⟨htr148a, htr148b, htr148c, _, _⟩ | ⟨htr148a, htr148b, htr148c, _, _⟩
          ·
            have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr048a, htr048b, htr048c, _, _⟩
              linarith only [hlam, htr014c, htr048a, htr148a])
            obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr046c, htr048b, htr068c])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr047c, htr048b, htr078c])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, htr046b, htr068a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc678xy, htr014c, htr046a, htr148a, htr467a, htr468c])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, htr047b, htr078a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd34a, hd56b, htr145a, htr148a, htr345a, htr468c, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34a, hd68b, htr345a, htr456b, htr467a, htr567a, htr568a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a]
            ·
              linarith only [hlam, hd34a, hd67b, htr145a, htr148a, htr345a, htr478c, htr678a]
          ·
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              rcases m.htr 1 4 9 (by decide) (by decide) with
                ⟨htr149a, htr149b, htr149c, _, _⟩ | ⟨htr149a, htr149b, htr149c, _, _⟩
              ·
                have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr049a, htr049b, htr049c, _, _⟩
                  linarith only [hlam, htr014c, htr049a, htr149a])
                obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr046c, htr049b, htr069c])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, htr047c, htr049b, htr079c])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, htr046b, htr069a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc679xy, htr014c, htr046a, htr149a, htr467a, htr469c])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, htr047b, htr079a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr145a, htr149a, htr345a, htr469c, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd34a, hd69b, htr345a, htr456b, htr467a, htr567a, htr569a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd79b, htr345a, htr456a, htr567a, htr679a]
                ·
                  linarith only [hlam, hd34a, hd67b, htr145a, htr149a, htr345a, htr479c, htr679a]
              ·
                rcases m.htr 4 5 10 (by decide) (by decide) with
                  ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                ·
                  rcases m.htr 1 4 10 (by decide) (by decide) with
                    ⟨htr1410a, htr1410b, htr1410c, _, _⟩ | ⟨htr1410a, htr1410b, htr1410c, _, _⟩
                  ·
                    have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                      linarith only [hlam, htr014c, htr0410a, htr1410a])
                    obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
                    have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                      linarith only [hlam, htr0410b, htr046c, htr0610c])
                    obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0410b, htr047c, htr0710c])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                      linarith only [hlam, htr046b, htr0610a, htr4610a])
                    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc6710xy, htr014c, htr046a, htr1410a, htr4610c, htr467a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                      linarith only [hlam, htr047b, htr0710a, htr4710a])
                    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                      linarith only [hlam, hd34a, hd56b, htr1410a, htr145a, htr345a, htr4610c, htr5610a])
                    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hd34a, hd610b, htr345a, htr456b, htr467a, htr5610a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    rcases m.htr 6 7 10 (by decide) (by decide) with
                      ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    ·
                      linarith only [hlam, hd34a, hd710b, htr345a, htr456a, htr567a, htr6710a]
                    ·
                      linarith only [hlam, hd34a, hd67b, htr1410a, htr145a, htr345a, htr4710c, htr6710a]
                  ·
                    rcases m.htr 5 6 7 (by decide) (by decide) with
                      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                    ·
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc012xy, hc679yx, htr015a, htr023a, htr156a, htr236a, htr369a, htr567a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc134zy, htr146a, htr346b, htr368a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc134zy, htr146a, htr346b, htr369a, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr468a, htr567a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc012xy, hc678zy, htr015a, htr023a, htr156a, htr237a, htr378a, htr568a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc134zy, htr147a, htr347b, htr378a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr469a, htr567a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012xy, hc689zy, htr015a, htr023a, htr156a, htr238a, htr389a, htr569a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd34a, hd89b, htr345a, htr456a, htr568a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd68b, htr345a, htr457b, htr478a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
                    ·
                      rcases m.htr 3 6 7 (by decide) (by decide) with
                        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                      ·
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc134zy, htr146a, htr346b, htr367a, htr467a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, hc134zy, htr016c, htr067a, htr146c, htr345a, htr456b, htr467a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, hc134zy, htr146c, htr167a, htr345a, htr456b, htr467a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                          linarith only [hlam, hd34a, hd68b, htr345a, htr456b, htr467a, htr567a, htr568a])
                        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                        rcases m.htr 4 6 8 (by decide) (by decide) with
                          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, hc456yz, htr067a, htr068a, htr468a, htr567a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, hc456yz, htr167a, htr168a, htr468a, htr567a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, htr236b, htr246c, htr368a, htr468a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          rcases m.htr 4 6 9 (by decide) (by decide) with
                            ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                          ·
                            rcases m.htr 4 6 10 (by decide) (by decide) with
                              ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                            ·
                              rcases m.htr 6 7 8 (by decide) (by decide) with
                                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                              ·
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789yx, htr016a, htr023a, htr167a, htr237a, htr379a, htr678a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                                  linarith only [hlam, hc356yz, htr067c, htr079a, htr367b, htr379a, htr567a])
                                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                                  linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
                                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                                  linarith only [hlam, hd34a, hd78b, htr045b, htr057b, htr079a, htr345a, htr578a, htr579a])
                                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                                  linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a])
                                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd34a, hd89b, htr345a, htr456b, htr467a, htr678a, htr789a]
                                ·
                                  linarith only [hlam, hd34a, hd78b, htr345a, htr456b, htr468a, htr689a, htr789a]
                              ·
                                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                                  linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
                                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789xy, htr016a, htr023a, htr167a, htr237a, htr378a, htr679a])
                                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
                                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                                  linarith only [hlam, hc012xy, hc578zy, htr018a, htr023a, htr189a, htr237a, htr378a, htr589a])
                                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc356yz, htr168c, htr189a, htr368b, htr389a, htr568a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
                                ·
                                  linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
                            ·
                              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                                linarith only [hlam, htr046b, htr0610a, htr4610a])
                              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                                linarith only [hlam, htr0610c, htr067b, htr0710b])
                              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                              have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                                linarith only [hlam, htr0610c, htr068b, htr0810b])
                              obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                              have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                                linarith only [hlam, hc356yz, htr067c, htr0710a, htr367b, htr3710a, htr567a])
                              obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                              have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                                linarith only [hlam, hc356yz, htr068c, htr0810a, htr368b, htr3810a, htr568a])
                              obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                                linarith only [hlam, hc012xy, hc7810yx, htr016a, htr023a, htr167a, htr237a, htr3710a, htr678a])
                              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                                linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
                              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                              rcases m.htr 7 8 10 (by decide) (by decide) with
                                ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              ·
                                linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr3810a, htr7810a]
                              ·
                                linarith only [hlam, hd12b, hd810a, htr123a, htr237a, htr378a, htr7810a]
                          ·
                            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                              linarith only [hlam, htr046b, htr069a, htr469a])
                            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                              linarith only [hlam, htr067b, htr069c, htr079b])
                            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                              linarith only [hlam, htr068b, htr069c, htr089b])
                            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                              linarith only [hlam, hc356yz, htr067c, htr079a, htr367b, htr379a, htr567a])
                            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                              linarith only [hlam, hc356yz, htr068c, htr089a, htr368b, htr389a, htr568a])
                            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                              linarith only [hlam, hc012xy, hc789yx, htr016a, htr023a, htr167a, htr237a, htr379a, htr678a])
                            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
                            ·
                              linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, htr046b, htr068a, htr468a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, htr067b, htr068c, htr078b])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, htr146b, htr168a, htr468a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, hc356yz, htr368a, htr467a, htr468a, htr567a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                            linarith only [hlam, hc356yz, htr067c, htr078a, htr367b, htr378a, htr567a])
                          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc012xy, hc789xy, htr016a, htr023a, htr167a, htr237a, htr378a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                            linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
                          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc012xy, hc568zy, htr018a, htr023a, htr189a, htr236a, htr368a, htr589a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd56b, hd78a, htr167a, htr168c, htr189a, htr567a, htr789a]
                          ·
                            linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
                      ·
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, htr026b, htr067a, htr236b, htr367a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                          linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a])
                        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc134zy, htr147a, htr347b, htr378a, htr478a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hc134zy, htr147c, htr178a, htr345a, htr457b, htr478a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc012xy, hc567zy, htr017a, htr023a, htr178a, htr236a, htr367a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                          linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
                        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc012xy, hc789yx, htr015a, htr023a, htr157a, htr237a, htr379a, htr578a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                          linarith only [hlam, hc134zy, htr146a, htr346b, htr368a, htr468a])
                        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                          linarith only [hlam, hc134zy, htr016c, htr068a, htr146c, htr345a, htr456b, htr468a])
                        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr367b, htr379a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd34a, hd78b, htr045b, htr057b, htr079a, htr345a, htr578a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc678xy, htr367a, htr368b, htr389a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd34a, hd89b, htr345a, htr457a, htr578a, htr789a]
                        ·
                          linarith only [hlam, hd67a, hd78b, htr367a, htr368a, htr689a, htr789a]
                ·
                  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                    linarith only [hlam, htr045b, htr0510a, htr4510a])
                  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr0510c, htr056b, htr0610b])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                    linarith only [hlam, htr0510c, htr057b, htr0710b])
                  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
                    linarith only [hlam, hc134zy, htr145a, htr235b, htr2510a, htr345b, htr4510a])
                  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
                  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                    linarith only [hlam, hc5610yx, htr056c, htr0610a, htr2510a, htr256b, htr2610a])
                  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc5710yx, htr057c, htr0710a, htr2510a, htr257b, htr2710a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                    linarith only [hlam, hc134zy, htr145a, htr345b, htr3510a, htr4510a])
                  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
                  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                    linarith only [hlam, hc134zy, htr146a, htr246c, htr2610a, htr346b, htr3610a])
                  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                    linarith only [hlam, hc134zy, htr147a, htr247c, htr2710a, htr347b, htr3710a])
                  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hc012xy, hc6710yx, htr015a, htr023a, htr156a, htr236a, htr3610a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc5610yx, htr3510a, htr356b, htr367a, htr567a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  rcases m.htr 6 7 10 (by decide) (by decide) with
                    ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                  ·
                    linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr3710a, htr6710a]
                  ·
                    linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
            ·
              have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                linarith only [hlam, htr045b, htr059a, htr459a])
              obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056b, htr059c, htr069b])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr057b, htr059c, htr079b])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr259a, htr259b, htr259c, _, _⟩
                linarith only [hlam, hc134zy, htr145a, htr235b, htr259a, htr345b, htr459a])
              obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc569yx, htr056c, htr069a, htr256b, htr259a, htr269a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc579yx, htr057c, htr079a, htr257b, htr259a, htr279a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                linarith only [hlam, hc134zy, htr145a, htr345b, htr359a, htr459a])
              obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc134zy, htr146a, htr246c, htr269a, htr346b, htr369a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc134zy, htr147a, htr247c, htr279a, htr347b, htr379a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hc012xy, hc679yx, htr015a, htr023a, htr156a, htr236a, htr369a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc569yx, htr356b, htr359a, htr367a, htr567a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr379a, htr679a]
              ·
                linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a]
        ·
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr045b, htr058a, htr458a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr056b, htr058c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr057b, htr058c, htr078b])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc134zy, htr145a, htr235b, htr258a, htr345b, htr458a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc568yx, htr056c, htr068a, htr256b, htr258a, htr268a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc578yx, htr057c, htr078a, htr257b, htr258a, htr278a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc134zy, htr145a, htr345b, htr358a, htr458a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hc134zy, htr146a, htr246c, htr268a, htr346b, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc134zy, htr147a, htr247c, htr278a, htr347b, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc568yx, htr356b, htr358a, htr367a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
          ·
            linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr046a, htr047a, htr456b, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045b, htr057a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr056b, htr057c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr145b, htr157a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc567yx, htr245a, htr247a, htr456a, htr457b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc134zy, htr145a, htr235b, htr257a, htr345b, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc567yx, htr056c, htr067a, htr256b, htr257a, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc134zy, htr145a, htr345b, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc134zy, htr146a, htr246c, htr267a, htr346b, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc012xy, hc678xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc567yx, htr045b, htr056b, htr068a, htr457a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr046c, htr048b, htr068c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc567yx, htr356b, htr357a, htr368a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc012xy, hc679xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc567yx, htr356b, htr357a, htr369a, htr569a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr123a, htr235a, htr357a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc567yx, htr056a, htr057c, htr078a, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc567yx, htr156a, htr157c, htr178a, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc478yz, htr047b, htr078a, htr247a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr234b, htr248a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr123a, htr238a, htr389a, htr689a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc034zy, htr048a, htr348b, htr389a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc124zy, htr148c, htr189a, htr248a, htr489a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc012xy, hc689yz, htr017a, htr023a, htr178a, htr236a, htr369a, htr789a]
      ·
        linarith only [hlam, hc012xy, hc678yz, htr018a, htr023a, htr189a, htr236a, htr368a, htr789a]

theorem shard_229 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False :=
  proof_shard_229 m htr014c htr015a htr015c htr016a htr016c htr017a htr018a htr023a htr026b htr045a htr045b htr123a htr145a htr145b htr145c htr234b htr235a htr235b htr236a htr236b htr237a htr238a htr245a htr245c htr345a htr345b htr345c htr456a htr456b htr456c

#print axioms shard_229
end Jsp404.NoSatElevenDBMTerminal
