import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_161 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr039c : m.d 0 9 < m.d 3 9)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr149b : m.d 1 4 < m.d 1 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348b : m.d 3 4 < m.d 3 8)
    (htr349a : m.d 3 4 + lam ≤ m.d 4 9)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
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
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr035c, htr056a, htr356a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc123zy, htr135c, htr156a, htr234a, htr345b, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd23a, hd57b, htr234a, htr345b, htr356a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd23a, hd58b, htr234a, htr345b, htr356a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd23a, hd59b, htr234a, htr345b, htr356a, htr456a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  rcases m.htr 3 5 7 (by decide) (by decide) with
    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr035c, htr057a, htr357a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc345yz, htr156a, htr157a, htr357a, htr456a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr025b, htr035c, htr257a, htr357a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    rcases m.htr 3 5 8 (by decide) (by decide) with
      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035c, htr058a, htr358a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc345yz, htr156a, htr158a, htr358a, htr456a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 3 5 9 (by decide) (by decide) with
        ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
      ·
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr035c, htr059a, htr359a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        rcases m.htr 3 5 10 (by decide) (by decide) with
          ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd23a, hd46b, htr234a, htr345b, htr356a, htr467a, htr567a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr234a, htr345b, htr356a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd23a, hd67b, htr234a, htr345b, htr357a, htr578a, htr678a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc045yz, htr057b, htr078a, htr457a, htr578a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr234a, htr345b, htr356a, htr567a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd23a, hd67b, htr234a, htr345b, htr357a, htr579a, htr679a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hc045yz, htr057b, htr079a, htr457a, htr579a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr234a, htr345b, htr356a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hd23a, hd68b, htr234a, htr345b, htr358a, htr589a, htr689a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, hc045yz, htr058b, htr089a, htr458a, htr589a])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd23a, hd810b, htr234a, htr345b, htr356a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                linarith only [hlam, hd23a, hd68b, htr234a, htr345b, htr358a, htr5810a, htr6810a])
              obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
              have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                linarith only [hlam, hc045yz, htr058b, htr0810a, htr458a, htr5810a])
              obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc123zy, hc678zy, htr038c, htr089a, htr138a, htr234a, htr345b, htr356a, htr568a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hc123zy, hc689zy, htr037c, htr078a, htr137a, htr234a, htr346a, htr469a, htr789a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc123zy, hc678zy, htr038c, htr0810a, htr138a, htr234a, htr345b, htr356a, htr568a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc123zy, hc8910yz, htr037c, htr078a, htr137a, htr234a, htr349a, htr4910a, htr7810a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679yx, htr467a, htr469c, htr4910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd67b, hd89a, htr467a, htr469a, htr6910a, htr8910a]
              ·
                linarith only [hlam, hd45b, hd910a, htr457a, htr578a, htr789a, htr8910a]
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, htr456b, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 5 6 9 (by decide) (by decide) with
                ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc123zy, htr036c, htr069a, htr136a, htr234a, htr345b, htr356a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr068c, htr069b, htr089c])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc678yx, htr068b, htr089a, htr467a, htr468c, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910yx, htr036c, htr068a, htr136a, htr234a, htr348a, htr489a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc678yx, htr467a, htr468c, htr4810a, htr6810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd23a, hd910b, htr234a, htr345b, htr356a, htr569a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                  linarith only [hlam, hc689xy, htr068a, htr069b, htr0910a, htr6910a])
                obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc123zy, hc679zy, htr039c, htr0910a, htr139a, htr234a, htr345b, htr356a, htr569a, htr7910a]
                ·
                  linarith only [hlam, hc123zy, hc8910zy, htr037c, htr079a, htr137a, htr234a, htr348a, htr4810a, htr7910a]
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc678yx, htr068a, htr069a, htr567a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, htr456b, htr469a, htr569a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                rcases m.htr 5 6 10 (by decide) (by decide) with
                  ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                ·
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, hc123zy, htr036c, htr0610a, htr136a, htr234a, htr345b, htr356a, htr5610a])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, htr0610b, htr068c, htr0810c])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, htr0610b, htr069c, htr0910c])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc678yx, htr068b, htr0810a, htr467a, htr468c, htr4810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc679yx, htr069b, htr0910a, htr467a, htr469c, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910xy, htr036c, htr068a, htr136a, htr234a, htr348a, htr4810a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc678yx, htr467a, htr468c, htr489a, htr689a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                  ·
                    linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                ·
                  rcases m.htr 5 8 9 (by decide) (by decide) with
                    ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                  ·
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yx, htr036c, htr068a, htr136a, htr234a, htr345b, htr358a, htr589a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc678yx, htr467a, htr468c, htr4810a, htr6810a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910zy, htr036c, htr069a, htr136a, htr234a, htr348a, htr4810a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc679yx, htr467a, htr469c, htr4910a, htr6910a])
                    obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd23a, hd910b, htr234a, htr345b, htr358a, htr589a, htr8910a]
                    ·
                      linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                  ·
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910xy, htr036c, htr068a, htr136a, htr234a, htr348a, htr4810a, htr689a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc678yx, htr467a, htr468c, htr4810a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yz, htr036c, htr068a, htr136a, htr234a, htr349a, htr4910a, htr6810a])
                    obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc679yx, htr467a, htr469c, htr4910a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd45b, hd89a, htr456a, htr569a, htr6910a, htr8910a]
                    ·
                      linarith only [hlam, hd45b, hd910a, htr456a, htr568a, htr689a, htr8910a]
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc045yz, htr056b, htr067a, htr456a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, htr456b, htr467a, htr567a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc123zy, htr036c, htr068a, htr136a, htr234a, htr345b, htr356a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, htr067c, htr068b, htr078c])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd23a, hd46b, htr234a, htr345b, htr356a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc678xy, htr067b, htr078a, htr467c, htr468a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc123zy, hc789yx, htr036c, htr067a, htr136a, htr234a, htr347a, htr478a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc678xy, htr467c, htr468a, htr479a, htr679a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc123zy, hc7810yx, htr036c, htr067a, htr136a, htr234a, htr347a, htr478a, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                linarith only [hlam, hc678xy, htr467c, htr468a, htr4710a, htr6710a])
              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr234a, htr345b, htr356a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, hc678xy, htr067a, htr068b, htr089a, htr689a])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                linarith only [hlam, hd23a, hd79b, htr234a, htr345b, htr359a, htr5910a, htr7910a])
              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
              have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                linarith only [hlam, hc045yz, htr059b, htr0910a, htr459a, htr5910a])
              obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc123zy, hc789zy, htr039c, htr0910a, htr139a, htr234a, htr347a, htr479a, htr8910a]
              ·
                linarith only [hlam, hc123zy, hc7910zy, htr038c, htr089a, htr138a, htr234a, htr347a, htr4710a, htr8910a]
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc123zy, htr037c, htr078a, htr137a, htr234a, htr345b, htr357a, htr578a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd23a, hd47b, htr234a, htr345b, htr357a, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr234a, htr345b, htr357a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd23a, hd78b, htr234a, htr345b, htr358a, htr589a, htr789a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, hc045yz, htr058b, htr089a, htr458a, htr589a])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc123zy, hc678yz, htr038c, htr089a, htr138a, htr234a, htr345b, htr357a, htr578a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc123zy, hc789zy, htr036c, htr068a, htr136a, htr234a, htr347a, htr479a, htr689a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr478a, htr479a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hc045yz, htr057b, htr079a, htr157c, htr179a, htr457a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910xy, htr036c, htr068a, htr136a, htr234a, htr348a, htr4810a, htr689a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc789yx, htr078b, htr079a, htr0810a, htr478c, htr4810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc123zy, hc678yz, htr038c, htr0810a, htr138a, htr234a, htr345b, htr357a, htr578a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910yz, htr036c, htr068a, htr136a, htr234a, htr349a, htr4910a, htr6810a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc789yx, htr478a, htr479c, htr4910a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd78b, hd89a, htr478a, htr479a, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hd45b, hd910a, htr456a, htr568a, htr689a, htr8910a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc045yz, htr057b, htr078a, htr457a, htr578a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc245yz, htr257b, htr278a, htr457a, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, htr457b, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, hc679xy, htr067c, htr069a, htr078a, htr678a])
                  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd45b, hd79a, htr457a, htr578a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc123zy, htr037c, htr079a, htr137a, htr234a, htr345b, htr357a, htr579a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr078c, htr079b, htr089c])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hc467zy, htr078b, htr089a, htr478c, htr489a, htr678a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yx, htr037c, htr078a, htr137a, htr234a, htr348a, htr489a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc467zy, htr478c, htr4810a, htr678a, htr7810a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910zy, htr036c, htr069a, htr136a, htr234a, htr348a, htr4810a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                      linarith only [hlam, hc123zy, hc679yz, htr039c, htr0910a, htr139a, htr234a, htr345b, htr357a, htr579a, htr6910a])
                    obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                    ·
                      linarith only [hlam, hd67a, hd89b, htr027b, htr079b, htr0910a, htr278a, htr678a, htr8910a]
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc567zy, htr027b, htr079a, htr278a, htr579a, htr678a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, htr457b, htr479a, htr579a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    rcases m.htr 5 7 10 (by decide) (by decide) with
                      ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    ·
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, hc123zy, htr037c, htr0710a, htr137a, htr234a, htr345b, htr357a, htr5710a])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0710b, htr078c, htr0810c])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                        linarith only [hlam, htr0710b, htr079c, htr0910c])
                      obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hc467zy, htr078b, htr0810a, htr478c, htr4810a, htr678a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                        linarith only [hlam, hc467zy, htr079b, htr0910a, htr479c, htr4910a, htr679a])
                      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hc123zy, hc8910xy, htr037c, htr078a, htr137a, htr234a, htr348a, htr4810a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                      ·
                        linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                    ·
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910yx, htr037c, htr078a, htr137a, htr234a, htr348a, htr489a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                          linarith only [hlam, hc467zy, htr478c, htr4810a, htr678a, htr7810a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910zy, htr036c, htr069a, htr136a, htr234a, htr348a, htr4810a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hc123zy, hc689yz, htr039c, htr0910a, htr139a, htr234a, htr348a, htr489a, htr6910a])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc467zy, htr079b, htr0910a, htr479c, htr4910a, htr679a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                        ·
                          linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                      ·
                        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910xy, htr037c, htr078a, htr137a, htr234a, htr348a, htr4810a, htr789a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, hc467zy, htr078b, htr0810a, htr478c, htr4810a, htr678a])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd45b, hd68a, htr457a, htr578a, htr689a, htr789a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                          linarith only [hlam, hd13b, hd89a, htr038c, htr0810a, htr138a, htr6810a, htr689a])
                        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910yz, htr036c, htr068a, htr136a, htr234a, htr349a, htr4910a, htr6810a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc467zy, htr479c, htr4910a, htr679a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd45b, hd89a, htr457a, htr579a, htr7910a, htr8910a]
                        ·
                          linarith only [hlam, hd45b, hd910a, htr457a, htr578a, htr789a, htr8910a]
                ·
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc123zy, hc789xy, htr036c, htr067a, htr136a, htr234a, htr345b, htr357a, htr579a, htr678a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hc123zy, hc7810xy, htr036c, htr067a, htr136a, htr234a, htr345b, htr357a, htr5710a, htr678a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd45b, hd78a, htr457a, htr579a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123zy, hc789yz, htr036c, htr067a, htr136a, htr234a, htr348a, htr489a, htr679a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc123zy, hc478zy, htr036c, htr067a, htr134b, htr136a, htr148b, htr189a, htr234a, htr489a, htr678a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd45b, hd78a, htr457a, htr5710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123zy, hc7910yz, htr036c, htr067a, htr136a, htr234a, htr349a, htr4910a, htr6710a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd45b, hd910a, htr456a, htr567a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd45b, hd79a, htr158c, htr189a, htr458a, htr7910a, htr8910a]
        ·
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, hc045yz, htr0510a, htr3510a, htr356a, htr456a])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, htr0510c, htr056b, htr0610b])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0510c, htr057b, htr0710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
            linarith only [hlam, htr0510c, htr058b, htr0810b])
          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc123zy, htr036c, htr0610a, htr136a, htr234a, htr345b, htr356a, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc6710yx, htr135b, htr156a, htr3510a, htr5610b, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc123zy, htr037c, htr0710a, htr137a, htr234a, htr345b, htr357a, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc7810yx, htr135b, htr157a, htr3510a, htr5710b, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, hc123zy, htr038c, htr0810a, htr138a, htr234a, htr345b, htr358a, htr5810a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd45b, hd67a, htr3510a, htr356a, htr456a, htr5710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd45b, hd710a, htr457a, htr578a, htr6710a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd45b, hd78a, htr3510a, htr356a, htr456a, htr5810b, htr7810a]
          ·
            linarith only [hlam, hd45b, hd810a, htr456a, htr567a, htr678a, htr7810a]
      ·
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc045yz, htr059a, htr356a, htr359a, htr456a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, htr056b, htr059c, htr069b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr057b, htr059c, htr079b])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr135b, htr159a, htr359a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc123zy, htr036c, htr069a, htr136a, htr234a, htr345b, htr356a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc679yx, htr135b, htr156a, htr359a, htr567a, htr569b])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc045yz, htr056b, htr067a, htr456a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc123zy, htr037c, htr079a, htr137a, htr234a, htr345b, htr357a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
          linarith only [hlam, hc7910xy, htr135b, htr157a, htr359a, htr5710a, htr579b])
        obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd45b, hd910a, htr356a, htr359a, htr456a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc569yx, htr156a, htr159c, htr1910a, htr5910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd45b, hd67a, htr356a, htr359a, htr456a, htr579b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc123zy, hc479zy, htr036c, htr067a, htr134b, htr136a, htr149b, htr1910a, htr234a, htr4910a, htr679a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 6 7 10 (by decide) (by decide) with
          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        ·
          linarith only [hlam, hd45b, hd79a, htr457a, htr5710a, htr6710a, htr679a]
        ·
          linarith only [hlam, hc123zy, hc7910yz, htr036c, htr067a, htr136a, htr234a, htr349a, htr4910a, htr6710a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc045yz, htr058a, htr356a, htr358a, htr456a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr056b, htr058c, htr068b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr057b, htr058c, htr078b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr135b, htr158a, htr358a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc123zy, htr036c, htr068a, htr136a, htr234a, htr345b, htr356a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc678yx, htr135b, htr156a, htr358a, htr567a, htr568b])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc045yz, htr056b, htr067a, htr456a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc123zy, htr037c, htr078a, htr137a, htr234a, htr345b, htr357a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc789xy, htr135b, htr157a, htr358a, htr578b, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd45b, hd89a, htr356a, htr358a, htr456a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc568yx, htr156a, htr158c, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr356a, htr358a, htr456a, htr578b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc123zy, hc478zy, htr036c, htr067a, htr134b, htr136a, htr148b, htr189a, htr234a, htr489a, htr678a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        linarith only [hlam, hd45b, hd78a, htr457a, htr579a, htr678a, htr679a]
      ·
        linarith only [hlam, hc123zy, hc789yz, htr036c, htr067a, htr136a, htr234a, htr348a, htr489a, htr679a]
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc045yz, htr057a, htr356a, htr357a, htr456a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr056b, htr057c, htr067b])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr135b, htr157a, htr357a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc123zy, htr036c, htr067a, htr136a, htr234a, htr345b, htr356a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc678xy, htr135b, htr156a, htr357a, htr567b, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc045yz, htr056b, htr068a, htr456a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc679xy, htr135b, htr156a, htr357a, htr567b, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
      linarith only [hlam, hc045yz, htr056b, htr069a, htr456a, htr569a])
    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd45b, hd78a, htr356a, htr357a, htr456a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc567yx, htr156a, htr157c, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd45b, hd79a, htr356a, htr357a, htr456a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc567yx, htr156a, htr157c, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd45b, hd710a, htr356a, htr357a, htr456a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
      linarith only [hlam, hc567yx, htr156a, htr157c, htr1710a, htr5710a])
    obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr478a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hd01a, hd78b, htr017a, htr1710a, htr4710a, htr478a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc123zy, hc789zy, htr036c, htr068a, htr136a, htr234a, htr347a, htr479a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc123zy, hc678yz, htr138a, htr234a, htr347a, htr389a, htr478a, htr689a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc123zy, hc7910zy, htr036c, htr069a, htr136a, htr234a, htr347a, htr4710a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd79b, htr234a, htr348b, htr389a, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc457zy, htr057a, htr058a, htr478a, htr578c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd01a, hd79b, htr017a, htr178a, htr478a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc457zy, htr057a, htr059a, htr479a, htr579c])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd45b, hd89a, htr035c, htr058a, htr356a, htr456a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd45b, hd910a, htr035c, htr059a, htr356a, htr456a, htr5910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc457zy, htr479a, htr579b, htr5910a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd910b, htr017a, htr178a, htr789a, htr8910a]
      ·
        linarith only [hlam, hd01a, hd89b, htr017a, htr179a, htr7910a, htr8910a]

theorem shard_161 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr039c : m.d 0 9 < m.d 3 9)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr149b : m.d 1 4 < m.d 1 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348b : m.d 3 4 < m.d 3 8)
    (htr349a : m.d 3 4 + lam ≤ m.d 4 9)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    : False :=
  proof_shard_161 m htr017a htr025b htr027b htr035c htr036c htr037c htr038c htr039c htr134b htr135b htr135c htr136a htr137a htr138a htr139a htr148b htr149b htr234a htr345b htr346a htr347a htr348a htr348b htr349a htr356a htr456a htr456b

#print axioms shard_161
end Jsp404.NoSatElevenDBMTerminal
