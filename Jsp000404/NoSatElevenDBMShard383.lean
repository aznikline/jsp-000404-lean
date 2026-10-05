import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_383 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047b : m.d 0 4 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < 4*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
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
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr136a, htr234a, htr236a, htr345a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr137a, htr234a, htr237a, htr345a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr138a, htr234a, htr238a, htr345a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr239a, htr239b, htr239c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr139a, htr234a, htr239a, htr345a])
  obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr123a, htr234a, htr345a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd12a, hd57b, htr123a, htr234a, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr157a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd12a, hd58b, htr123a, htr234a, htr345a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr158a, htr458a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd12a, hd59b, htr123a, htr234a, htr345a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr159a, htr459a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr123a, htr234a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr123a, htr234a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd12a, hd69b, htr123a, htr234a, htr346a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr123a, htr234a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr123a, htr234a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc456zy, htr346a, htr348a, htr468b, htr568a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr123a, htr234a, htr348a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd12a, hd810b, htr123a, htr234a, htr348a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hc456zy, htr468c, htr4810a, htr568a, htr6810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, hc456zy, htr468a, htr568b, htr5810a, htr6810a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc125xy, hc478zy, htr123a, htr158a, htr234a, htr348a, htr589a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr349a, htr349b, htr349c, _, _⟩
            linarith only [hlam, hc125xy, hc489zy, htr123a, htr157a, htr234a, htr349a, htr578a, htr789a])
          obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc456zy, htr346a, htr349a, htr469b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd46b, hd910a, htr467a, htr567a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd45b, hd69a, htr345a, htr349a, htr4910a, htr6910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc145xy, hc389zy, htr149a, htr157a, htr3910a, htr4910a, htr578a, htr789a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hc125xy, hc478zy, htr123a, htr158a, htr234a, htr348a, htr5810a, htr7810a]
          ·
            linarith only [hlam, hc125xy, hc8910yz, htr123a, htr157a, htr239a, htr3910a, htr578a, htr7810a]
        ·
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hd46b, hd89a, htr467a, htr567a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hd46b, hd810a, htr467a, htr567a, htr568a, htr6810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr349a, htr349b, htr349c, _, _⟩
              linarith only [hlam, hc456zy, htr346a, htr349a, htr469b, htr569a])
            obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc368zy, htr389a, htr568a, htr569a, htr689c])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc468zy, htr489a, htr568a, htr569a, htr689c])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr348a, htr348b, htr348c, _, _⟩
              linarith only [hlam, hd12a, hd89b, htr123a, htr234a, htr348a, htr489a])
            obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
              linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr4810a, htr6810a])
            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
            have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
              linarith only [hlam, hd14a, hd89b, htr148a, htr3810a, htr389a, htr4810a])
            obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hd12a, hd910b, htr123a, htr234a, htr349a, htr4910a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc456zy, htr469c, htr4910a, htr569a, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
              linarith only [hlam, hc456zy, htr469a, htr569b, htr5910a, htr6910a])
            obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
            rcases m.htr 7 9 10 (by decide) (by decide) with
              ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            ·
              linarith only [hlam, hc125xy, hc479zy, htr123a, htr159a, htr234a, htr349a, htr5910a, htr7910a]
            ·
              linarith only [hlam, hc125xy, hc8910zy, htr123a, htr157a, htr238a, htr3810a, htr579a, htr7910a]
          ·
            rcases m.htr 3 4 8 (by decide) (by decide) with
              ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
            ·
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hc125xy, hc468zy, htr015a, htr016a, htr123a, htr156b, htr234a, htr348a, htr568a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              rcases m.htr 1 6 7 (by decide) (by decide) with
                ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr167a, htr467a]
              ·
                linarith only [hlam, hc126xy, hc468zy, htr123a, htr167a, htr234a, htr348a, htr567a, htr568a]
            ·
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr489a, htr689a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc134yz, htr148a, htr348c, htr389a, htr489a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hc125xy, hc689yz, htr015a, htr016a, htr123a, htr156b, htr238a, htr389a, htr569a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              rcases m.htr 1 6 7 (by decide) (by decide) with
                ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr167a, htr467a]
              ·
                linarith only [hlam, hc126xy, hc689yz, htr123a, htr167a, htr238a, htr389a, htr567a, htr569a]
      ·
        have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr016a, htr016b, htr016c, _, _⟩
          linarith only [hlam, hc125xy, hc467zy, htr015a, htr016a, htr123a, htr156b, htr234a, htr347a, htr567a])
        obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr168a, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr169a, htr469a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc126xy, hc467zy, htr123a, htr168a, htr234a, htr347a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc126xy, hc467zy, htr123a, htr169a, htr234a, htr347a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc467zy, htr347a, htr348a, htr478b, htr678a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr123a, htr234a, htr348a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd12a, hd810b, htr123a, htr234a, htr348a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr349a, htr349b, htr349c, _, _⟩
            linarith only [hlam, hc125xy, hc489zy, htr123a, htr156a, htr234a, htr349a, htr568a, htr689a])
          obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc467zy, htr478c, htr4810a, htr678a, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hc467zy, htr478a, htr678b, htr6810a, htr7810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc125xy, hc8910yz, htr123a, htr156a, htr239a, htr3910a, htr568a, htr6810a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hc145xy, hc389zy, htr149a, htr156a, htr3910a, htr4910a, htr568a, htr689a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd45b, hd89a, htr345a, htr349a, htr4910a, htr8910a]
          ·
            linarith only [hlam, hd45b, hd910a, htr456a, htr568a, htr689a, htr8910a]
        ·
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, hc125xy, hc478zy, htr123a, htr156a, htr234a, htr348a, htr567a, htr678a])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr018a, htr018b, htr018c, _, _⟩
            linarith only [hlam, hc134yz, htr014a, htr018a, htr148c, htr348a])
          obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr124a, htr248a, htr345a, htr348a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd45b, hd78a, htr345a, htr348a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc145xy, hc378zy, htr148a, htr156a, htr389a, htr489a, htr567a, htr678a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
            linarith only [hlam, hc125xy, hc8910yx, htr015a, htr018a, htr123a, htr1810a, htr238a, htr389a])
          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc134yz, htr148b, htr1810a, htr348a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hc145xy, hc378zy, htr148a, htr156a, htr3810a, htr4810a, htr567a, htr678a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc125xy, hc789yz, htr123a, htr156a, htr238a, htr389a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, hc467zy, htr234c, htr249a, htr347a, htr479b, htr679a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd14a, hd910b, htr148a, htr248a, htr249a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc125xy, hc8910zy, htr123a, htr156a, htr238a, htr3810a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            linarith only [hlam, hc467zy, htr479c, htr4910a, htr679a, htr7910a]
          ·
            linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc134yz, htr014a, htr017a, htr147c, htr347a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hd12a, hd45b, htr124a, htr247a, htr345a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr234c, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr247c, htr248b, htr278c])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr127a, htr278a, htr345a, htr347c, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc125xy, hc789yx, htr015a, htr017a, htr123a, htr179a, htr237a, htr378a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
          linarith only [hlam, hc125xy, hc7810yx, htr015a, htr017a, htr123a, htr1710a, htr237a, htr378a])
        obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, htr247b, htr278a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc134yz, htr147b, htr179a, htr347a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc134yz, htr147a, htr347c, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hc134yz, htr147b, htr1710a, htr347a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, hc134yz, htr147a, htr347c, htr3710a, htr4710a])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr123a, htr234a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, htr478c, htr489a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr123a, htr237a, htr379a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hc125xy, hc7910zy, htr123a, htr158a, htr237a, htr3710a, htr589a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hc125xy, hc789zy, htr123a, htr159a, htr237a, htr379a, htr5910a, htr8910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            rcases m.htr 6 9 10 (by decide) (by decide) with
              ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            ·
              linarith only [hlam, hd67a, hd79b, htr567a, htr569a, htr6910a, htr7910a]
            ·
              linarith only [hlam, hc456zy, htr469a, htr569b, htr5910a, htr6910a]
          ·
            have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr016a, htr016b, htr016c, _, _⟩
              linarith only [hlam, hc125xy, hc679yz, htr015a, htr016a, htr123a, htr156b, htr237a, htr379a, htr569a])
            obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
            rcases m.htr 1 6 8 (by decide) (by decide) with
              ⟨htr168a, htr168b, htr168c, _, _⟩ | ⟨htr168a, htr168b, htr168c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr168a, htr468a]
            ·
              linarith only [hlam, hc126xy, hc679yz, htr123a, htr168a, htr237a, htr379a, htr568a, htr569a]
        ·
          have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr016a, htr016b, htr016c, _, _⟩
            linarith only [hlam, hc125xy, hc468zy, htr015a, htr016a, htr123a, htr156b, htr234a, htr348a, htr568a])
          obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr169a, htr469a])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc126xy, hc468zy, htr123a, htr169a, htr234a, htr348a, htr568a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc125xy, hc789zy, htr123a, htr156a, htr237a, htr379a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc125xy, hc7910zy, htr123a, htr156a, htr237a, htr3710a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc468zy, htr489a, htr689b, htr6910a, htr8910a]
      ·
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc134yz, htr014a, htr018a, htr148c, htr348a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc146yz, htr168a, htr346a, htr348a, htr468b])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc134yz, htr147a, htr247a, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        rcases m.htr 0 1 6 (by decide) (by decide) with
          ⟨htr016a, htr016b, htr016c, _, _⟩ | ⟨htr016a, htr016b, htr016c, _, _⟩
        ·
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr249a, htr249b, htr249c, _, _⟩
              linarith only [hlam, htr234c, htr249a, htr349a])
            obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, htr247c, htr249b, htr279c])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
              linarith only [hlam, htr248c, htr249b, htr289c])
            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr127a, htr279a, htr345a, htr347c, htr379a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc125xy, hc789xy, htr015a, htr017a, htr123a, htr178a, htr237a, htr379a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr128a, htr289a, htr345a, htr348c, htr389a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc134yz, htr147b, htr178a, htr347a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
            ·
              linarith only [hlam, hd12a, hd78b, htr123a, htr238a, htr389a, htr789a]
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
                linarith only [hlam, htr234c, htr2410a, htr3410a])
              obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
              have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                linarith only [hlam, htr2410b, htr247c, htr2710c])
              obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
              have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                linarith only [hlam, htr2410b, htr248c, htr2810c])
              obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
              have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr127a, htr2710a, htr345a, htr347c, htr3710a])
              obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc125xy, hc7810xy, htr015a, htr017a, htr123a, htr178a, htr237a, htr3710a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                linarith only [hlam, hd12a, hd45b, htr128a, htr2810a, htr345a, htr348c, htr3810a])
              obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc134yz, htr147b, htr178a, htr347a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 7 8 10 (by decide) (by decide) with
                ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd810b, htr123a, htr237a, htr378a, htr7810a]
              ·
                linarith only [hlam, hd12a, hd78b, htr123a, htr238a, htr3810a, htr7810a]
            ·
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc125xy, hc789yx, htr015a, htr017a, htr123a, htr179a, htr237a, htr378a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc134yz, htr147b, htr179a, htr347a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc134yz, htr147a, htr347c, htr379a, htr479a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc125xy, hc789zy, htr015a, htr018a, htr123a, htr189a, htr237a, htr379a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc134yz, htr148b, htr189a, htr348a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc134yz, htr148a, htr348c, htr389a, htr489a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd12a, hd78b, htr123a, htr238a, htr389a, htr789a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc034yz, htr047b, htr078a, htr347a, htr478a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc134yz, htr147b, htr178a, htr347a, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc125xy, hc789xy, htr015a, htr017a, htr123a, htr178a, htr237a, htr379a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hd45b, hd78a, htr078a, htr079a, htr345a, htr347c, htr379a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hd45b, hd78a, htr047c, htr079a, htr178a, htr179a, htr345a, htr347a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc125xy, hc789yz, htr015a, htr017a, htr123a, htr179a, htr238a, htr389a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc134yz, htr148a, htr348c, htr389a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd45b, hd78a, htr345a, htr348a, htr489a, htr789a]
                ·
                  linarith only [hlam, hd45b, hd89a, htr345a, htr347a, htr478a, htr789a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc125xy, hc678yz, htr015a, htr016a, htr123a, htr168a, htr237a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a]
          ·
            linarith only [hlam, hd15b, hd78a, htr015a, htr016a, htr156b, htr567a, htr678a]
  ·
    have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr016a, htr016b, htr016c, _, _⟩
      linarith only [hlam, hc134yz, htr014a, htr016a, htr146c, htr346a])
    obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr124a, htr246a, htr345a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr234c, htr247a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr246c, htr247b, htr267c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd12a, hd45b, htr126a, htr267a, htr345a, htr346c, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc125xy, hc678yx, htr015a, htr016a, htr123a, htr168a, htr236a, htr367a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc125xy, hc679yx, htr015a, htr016a, htr123a, htr169a, htr236a, htr367a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc125xy, hc6710yx, htr015a, htr016a, htr123a, htr1610a, htr236a, htr367a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr246b, htr267a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc134yz, htr146b, htr168a, htr346a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc134yz, htr146a, htr346c, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc134yz, htr146b, htr169a, htr346a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc134yz, htr146a, htr346c, htr369a, htr469a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
        linarith only [hlam, hc134yz, htr146b, htr1610a, htr346a, htr4610a])
      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
      have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
        linarith only [hlam, hc134yz, htr146a, htr346c, htr3610a, htr4610a])
      obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr123a, htr234a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr123a, htr234a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr467c, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, htr467c, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr123a, htr236a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd12a, hd910b, htr123a, htr236a, htr369a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc125xy, hc6910zy, htr123a, htr158a, htr236a, htr3610a, htr589a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc125xy, hc689zy, htr123a, htr159a, htr236a, htr369a, htr5910a, htr8910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc167yz, htr179a, htr679c, htr6910a, htr7910a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr017a, htr017b, htr017c, _, _⟩
            linarith only [hlam, hc125xy, hc679zy, htr015a, htr017a, htr123a, htr179a, htr236a, htr369a])
          obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd12a, hd47b, htr012a, htr017a, htr178a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 5 7 9 (by decide) (by decide) with
            ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
          ·
            linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
          ·
            linarith only [hlam, hc127xy, hc679zy, htr123a, htr178a, htr236a, htr369a, htr578a, htr579a]
        ·
          rcases m.htr 5 7 9 (by decide) (by decide) with
            ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
          ·
            linarith only [hlam, hc457zy, htr479a, htr579b, htr5910a, htr7910a]
          ·
            linarith only [hlam, hc125xy, hc689zy, htr123a, htr157a, htr236a, htr369a, htr579a, htr7910a, htr8910a]
      ·
        have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr017a, htr017b, htr017c, _, _⟩
          linarith only [hlam, hc125xy, hc678zy, htr015a, htr017a, htr123a, htr157b, htr236a, htr368a, htr578a])
        obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hd12a, hd47b, htr012a, htr017a, htr179a, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc127xy, hc678zy, htr123a, htr179a, htr236a, htr368a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc125xy, hc689zy, htr123a, htr157a, htr236a, htr369a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc125xy, hc6910zy, htr123a, htr157a, htr236a, htr3610a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
    ·
      have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr017a, htr017b, htr017c, _, _⟩
        linarith only [hlam, hc134yz, htr014a, htr017a, htr147c, htr347a])
      obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc134yz, htr146a, htr246a, htr247a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr234c, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr246c, htr248b, htr268c])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr247c, htr248b, htr278c])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr126a, htr268a, htr345a, htr346c, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc125xy, hc678xy, htr015a, htr016a, htr123a, htr167a, htr236a, htr368a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd12a, hd45b, htr127a, htr278a, htr345a, htr347c, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc134yz, htr146a, htr346c, htr367a, htr467a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a]
        ·
          linarith only [hlam, hd12a, hd67b, htr123a, htr237a, htr378a, htr678a]
      ·
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, htr234c, htr249a, htr349a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, htr246c, htr249b, htr269c])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, htr247c, htr249b, htr279c])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr126a, htr269a, htr345a, htr346c, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc125xy, hc679xy, htr015a, htr016a, htr123a, htr167a, htr236a, htr369a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12a, hd45b, htr127a, htr279a, htr345a, htr347c, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc134yz, htr146a, htr346c, htr367a, htr467a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd79b, htr123a, htr236a, htr367a, htr679a]
          ·
            linarith only [hlam, hd12a, hd67b, htr123a, htr237a, htr379a, htr679a]
        ·
          rcases m.htr 3 4 10 (by decide) (by decide) with
            ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
          ·
            have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
              linarith only [hlam, htr234c, htr2410a, htr3410a])
            obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
            have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
              linarith only [hlam, htr2410b, htr246c, htr2610c])
            obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, htr2410b, htr247c, htr2710c])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr126a, htr2610a, htr345a, htr346c, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc125xy, hc6710xy, htr015a, htr016a, htr123a, htr167a, htr236a, htr3610a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, hd12a, hd45b, htr127a, htr2710a, htr345a, htr347c, htr3710a])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc134yz, htr146a, htr346c, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd710b, htr123a, htr236a, htr367a, htr6710a]
            ·
              linarith only [hlam, hd12a, hd67b, htr123a, htr237a, htr3710a, htr6710a]
          ·
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc134yz, htr146a, htr346c, htr367a, htr467a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc125xy, hc678yx, htr015a, htr016a, htr123a, htr168a, htr236a, htr367a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc134yz, htr146b, htr168a, htr346a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc134yz, htr146a, htr346c, htr368a, htr468a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc125xy, hc678zy, htr015a, htr017a, htr123a, htr178a, htr236a, htr368a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc134yz, htr147b, htr178a, htr347a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a]
              ·
                linarith only [hlam, hd12a, hd67b, htr123a, htr237a, htr378a, htr678a]
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc034yz, htr046b, htr067a, htr346a, htr467a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc125xy, hc678xy, htr015a, htr016a, htr123a, htr167a, htr236a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr067a, htr068a, htr345a, htr346c, htr368a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr046c, htr068a, htr167a, htr168a, htr345a, htr346a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc125xy, hc678yz, htr015a, htr016a, htr123a, htr168a, htr237a, htr378a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a]
              ·
                linarith only [hlam, hd45b, hd78a, htr345a, htr346a, htr467a, htr678a]

theorem shard_383 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047b : m.d 0 4 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_383 m htr012a htr014a htr015a htr046b htr046c htr047b htr047c htr123a htr124a htr126a htr127a htr128a htr136a htr137a htr138a htr139a htr146a htr146b htr146c htr147a htr147b htr147c htr148a htr148b htr148c htr149a htr234a htr234c htr345a

#print axioms shard_383
end Jsp404.NoSatElevenDBMTerminal
