import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_473 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348c : m.d 3 8 < m.d 4 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd05a, hd05braw⟩ := m.hrange 0 5 (by decide)
  have hd05b : m.d 0 5 < 4*lam := by
    linarith only [hd05braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
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
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc346xy, htr035a, htr036a, htr134a, htr135a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc347xy, htr035a, htr037a, htr134a, htr135a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc348xy, htr035a, htr038a, htr134a, htr135a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  rcases m.htr 1 3 7 (by decide) (by decide) with
    ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc034zy, htr047a, htr134a, htr137a, htr347c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hc234zy, htr134a, htr137a, htr247a, htr347c])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 1 3 8 (by decide) (by decide) with
      ⟨htr138a, htr138b, htr138c, _, _⟩ | ⟨htr138a, htr138b, htr138c, _, _⟩
    ·
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc034zy, htr048a, htr134a, htr138a, htr348c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc234zy, htr134a, htr138a, htr248a, htr348c])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      rcases m.htr 1 3 9 (by decide) (by decide) with
        ⟨htr139a, htr139b, htr139c, _, _⟩ | ⟨htr139a, htr139b, htr139c, _, _⟩
      ·
        rcases m.htr 1 3 10 (by decide) (by decide) with
          ⟨htr1310a, htr1310b, htr1310c, _, _⟩ | ⟨htr1310a, htr1310b, htr1310c, _, _⟩
        ·
          rcases m.htr 3 5 6 (by decide) (by decide) with
            ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
          ·
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr356a, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34a, hd67b, htr134a, htr135a, htr356a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr367a, htr567a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd34a, hd68b, htr134a, htr135a, htr356a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr368a, htr568a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            rcases m.htr 4 5 7 (by decide) (by decide) with
              ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
            ·
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd34a, hd78b, htr134a, htr135a, htr345c, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr134a, htr137a, htr378a, htr578a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd34a, hd79b, htr134a, htr135a, htr345c, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr134a, htr137a, htr379a, htr579a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc023xy, hc567zy, htr024a, htr037a, htr245a, htr378a, htr457a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                linarith only [hlam, hc023xy, hc578zy, htr024a, htr036a, htr245a, htr367a, htr458a, htr678a])
              obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc023xy, hc567zy, htr024a, htr037a, htr245a, htr379a, htr457a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc023xy, hc789yz, htr024a, htr036a, htr248a, htr367a, htr489a, htr679a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568yx, htr456a, htr458c, htr489a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
              ·
                linarith only [hlam, hd23b, hd89a, htr236a, htr367a, htr678a, htr789a]
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd34a, hd56b, htr035b, htr057a, htr134a, htr135a, htr456a, htr457a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd34a, hd56b, htr134a, htr135b, htr157a, htr456a, htr457a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              rcases m.htr 4 5 8 (by decide) (by decide) with
                ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, htr045c, htr058a, htr458a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr057c, htr058b, htr078c])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, htr145c, htr158a, htr458a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr037b, htr078a, htr134a, htr137a, htr456a, htr457c, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc012yx, hc789yx, htr015a, htr024a, htr157a, htr247a, htr478a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hc567yx, htr047c, htr079a, htr456a, htr457c, htr579a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr037b, htr079a, htr134a, htr137a, htr456a, htr457c, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd34a, hd89b, htr134a, htr135a, htr345c, htr458a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc578xy, htr157a, htr158b, htr189a, htr589a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc012yx, hc568zy, htr018a, htr024a, htr189a, htr245a, htr458a, htr689a]
                ·
                  linarith only [hlam, hc023xy, hc789zy, htr024a, htr036a, htr247a, htr368a, htr479a, htr689a]
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr035b, htr058a, htr134a, htr135a, htr456a, htr458a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc567yx, htr157a, htr158a, htr456a, htr458a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                rcases m.htr 4 5 9 (by decide) (by decide) with
                  ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                ·
                  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                    linarith only [hlam, htr045c, htr059a, htr459a])
                  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, htr057c, htr059b, htr079c])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, htr058c, htr059b, htr089c])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hd34a, hd56b, htr037b, htr079a, htr134a, htr137a, htr456a, htr457c, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc012yx, hc789xy, htr015a, htr024a, htr157a, htr247a, htr479a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, hc567yx, htr047c, htr078a, htr456a, htr457c, htr578a])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd34a, hd89b, htr037b, htr078a, htr134a, htr137a, htr789a]
                  ·
                    linarith only [hlam, hd34a, hd78b, htr038b, htr089a, htr134a, htr138a, htr789a]
                ·
                  rcases m.htr 4 5 10 (by decide) (by decide) with
                    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                  ·
                    have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                      linarith only [hlam, htr045c, htr0510a, htr4510a])
                    obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0510b, htr057c, htr0710c])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, htr0510b, htr058c, htr0810c])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                      linarith only [hlam, hd34a, hd56b, htr037b, htr0710a, htr134a, htr137a, htr456a, htr457c, htr4710a])
                    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hc012yx, hc7810xy, htr015a, htr024a, htr157a, htr247a, htr4710a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc567yx, htr047c, htr078a, htr456a, htr457c, htr578a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd34a, hd810b, htr037b, htr078a, htr134a, htr137a, htr7810a]
                    ·
                      linarith only [hlam, hd34a, hd78b, htr038b, htr0810a, htr134a, htr138a, htr7810a]
                  ·
                    rcases m.htr 4 7 8 (by decide) (by decide) with
                      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                    ·
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc012yx, hc789yx, htr015a, htr024a, htr157a, htr247a, htr478a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc567yx, htr047c, htr079a, htr456a, htr457c, htr579a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd34a, hd56b, htr037b, htr079a, htr134a, htr137a, htr456a, htr457c, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc568yx, htr048c, htr089a, htr456a, htr458c, htr589a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd89b, htr134a, htr137a, htr347c, htr478a, htr789a]
                      ·
                        linarith only [hlam, hd34a, hd78b, htr038b, htr089a, htr134a, htr138a, htr789a]
                    ·
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hc012yx, hc789xy, htr015a, htr024a, htr157a, htr247a, htr479a, htr578a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc012yx, hc789yz, htr015a, htr024a, htr157a, htr248a, htr489a, htr579a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc568yx, htr456a, htr458c, htr489a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
                      ·
                        linarith only [hlam, hd56b, hd89a, htr456a, htr457a, htr578a, htr789a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr035b, htr056a, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc345xy, htr134a, htr135b, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, htr345c, htr356a, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            rcases m.htr 3 5 7 (by decide) (by decide) with
              ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd05b, hd34a, htr057a, htr134a, htr135a, htr357a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr056c, htr057b, htr067c])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, htr135c, htr157a, htr357a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr357a, htr457a])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr036b, htr067a, htr134a, htr136a, htr456c, htr457a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc023xy, hc678yx, htr024a, htr035a, htr246a, htr356a, htr467a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc567xy, htr056c, htr057a, htr068a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr036b, htr068a, htr134a, htr136a, htr456c, htr457a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc023xy, hc679yx, htr024a, htr035a, htr246a, htr356a, htr467a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc567xy, htr056c, htr057a, htr069a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr036b, htr069a, htr134a, htr136a, htr456c, htr457a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd34a, hd78b, htr134a, htr135a, htr357a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc567xy, htr156a, htr157b, htr178a, htr578a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd34a, hd89b, htr036b, htr068a, htr134a, htr136a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr134a, htr138a, htr389a, htr689a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc023xy, hc678zy, htr024a, htr038a, htr246a, htr389a, htr468a, htr789a]
              ·
                linarith only [hlam, hc012yx, hc689zy, htr017a, htr024a, htr178a, htr246a, htr469a, htr789a]
            ·
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, htr136c, htr167a, htr367a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34a, hd46b, htr134a, htr136a, htr367a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd34a, hd78b, htr134a, htr136a, htr367a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr134a, htr137a, htr378a, htr678a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc023xy, hc567yz, htr024a, htr037a, htr246a, htr378a, htr467a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc023xy, hc678zy, htr024a, htr035a, htr246a, htr357a, htr468a, htr578a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr134a, htr136b, htr168a, htr467a, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc023xy, hc789xy, htr024a, htr035a, htr247a, htr357a, htr479a, htr578a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc678yx, htr167b, htr168a, htr179a, htr467c, htr479a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc012yx, hc567yz, htr017a, htr024a, htr179a, htr246a, htr467a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc023xy, hc789yz, htr024a, htr035a, htr248a, htr357a, htr489a, htr579a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc678yx, htr467a, htr468c, htr489a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd67b, hd78a, htr467a, htr468a, htr689a, htr789a]
                ·
                  linarith only [hlam, hd23b, hd89a, htr235a, htr357a, htr578a, htr789a]
              ·
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, htr036b, htr067a, htr367a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc346xy, htr134a, htr136b, htr167a, htr367a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, htr346c, htr367a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                rcases m.htr 5 6 7 (by decide) (by decide) with
                  ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                ·
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hc568xy, htr156c, htr158a, htr167a, htr567a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd23b, hd68a, htr236a, htr367a, htr567a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  rcases m.htr 4 6 8 (by decide) (by decide) with
                    ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                  ·
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, htr046c, htr068a, htr468a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, htr067c, htr068b, htr078c])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, htr146c, htr168a, htr468a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd34a, hd68b, htr037b, htr078a, htr134a, htr137a, htr467c, htr468a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hc023xy, hc789yx, htr024a, htr036a, htr247a, htr367a, htr478a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc056zy, htr067c, htr079a, htr567a, htr679a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hd34a, hd68b, htr037b, htr079a, htr134a, htr137a, htr467c, htr468a, htr479a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc012yx, hc568yz, htr018a, htr024a, htr189a, htr246a, htr468a, htr589a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd34a, hd89b, htr037b, htr078a, htr134a, htr137a, htr789a]
                    ·
                      linarith only [hlam, hd56a, hd78b, htr167a, htr168b, htr189a, htr567a, htr789a]
                  ·
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, hc456zy, htr036b, htr068a, htr367a, htr468a, htr567a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc456zy, htr167a, htr168a, htr468a, htr567a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    rcases m.htr 4 6 9 (by decide) (by decide) with
                      ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                    ·
                      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                        linarith only [hlam, htr046c, htr069a, htr469a])
                      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr067c, htr069b, htr079c])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, htr068c, htr069b, htr089c])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd34a, hd69b, htr037b, htr079a, htr134a, htr137a, htr467c, htr469a, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc023xy, hc789xy, htr024a, htr036a, htr247a, htr367a, htr479a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc056zy, htr067c, htr078a, htr567a, htr678a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd89b, htr037b, htr078a, htr134a, htr137a, htr789a]
                      ·
                        linarith only [hlam, hd34a, hd78b, htr038b, htr089a, htr134a, htr138a, htr789a]
                    ·
                      rcases m.htr 4 6 10 (by decide) (by decide) with
                        ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                      ·
                        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                          linarith only [hlam, htr046c, htr0610a, htr4610a])
                        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr0610b, htr067c, htr0710c])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, htr0610b, htr068c, htr0810c])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                          linarith only [hlam, hd34a, hd610b, htr037b, htr0710a, htr134a, htr137a, htr4610a, htr467c, htr4710a])
                        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hc023xy, hc7810xy, htr024a, htr036a, htr247a, htr367a, htr4710a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, hc056zy, htr067c, htr078a, htr567a, htr678a])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        rcases m.htr 7 8 10 (by decide) (by decide) with
                          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        ·
                          linarith only [hlam, hd34a, hd810b, htr037b, htr078a, htr134a, htr137a, htr7810a]
                        ·
                          linarith only [hlam, hd34a, hd78b, htr038b, htr0810a, htr134a, htr138a, htr7810a]
                      ·
                        rcases m.htr 6 7 8 (by decide) (by decide) with
                          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                        ·
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, hc056zy, htr067c, htr078a, htr567a, htr678a])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc023xy, hc789yx, htr024a, htr036a, htr247a, htr367a, htr478a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                            linarith only [hlam, hc056zy, htr067c, htr079a, htr567a, htr679a])
                          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hd34a, hd78b, htr037b, htr079a, htr134a, htr137a, htr478a, htr479a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc012yx, hc578yz, htr018a, htr024a, htr189a, htr247a, htr478a, htr589a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                            linarith only [hlam, hc456zy, htr048c, htr089a, htr168b, htr189a, htr468c, htr568a])
                          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd34a, hd89b, htr037b, htr078a, htr134a, htr137a, htr789a]
                          ·
                            linarith only [hlam, hd34a, hd78b, htr038b, htr089a, htr134a, htr138a, htr789a]
                        ·
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hc023xy, hc789xy, htr024a, htr036a, htr247a, htr367a, htr479a, htr678a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                            linarith only [hlam, hc456zy, htr167b, htr179a, htr467c, htr479a, htr567a])
                          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hd23b, hd57a, htr236a, htr367a, htr578a, htr678a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr578a, htr579a])
                          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                            linarith only [hlam, hc023xy, hc789yz, htr024a, htr035a, htr248a, htr357a, htr489a, htr579a])
                          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
                          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd01b, hd78a, htr016a, htr168a, htr689a, htr789a]
                          ·
                            linarith only [hlam, hd23b, hd89a, htr236a, htr367a, htr678a, htr789a]
                ·
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc023xy, hc678xy, htr024a, htr035a, htr246a, htr356a, htr468a, htr567a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hd34a, hd46b, htr134a, htr136a, htr368a, htr468a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                    linarith only [hlam, hc023xy, hc679xy, htr024a, htr035a, htr246a, htr356a, htr469a, htr567a])
                  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                    linarith only [hlam, hd34a, hd46b, htr134a, htr136a, htr369a, htr469a])
                  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd23b, hd67a, htr236a, htr368a, htr567a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc023xy, hc678yz, htr024a, htr035a, htr247a, htr356a, htr478a, htr568a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr378a, htr478a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                    linarith only [hlam, hd23b, hd67a, htr236a, htr369a, htr567a, htr569a])
                  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc023xy, hc689yz, htr024a, htr035a, htr248a, htr356a, htr489a, htr569a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd23b, hd89a, htr235a, htr356a, htr568a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a]
                  ·
                    linarith only [hlam, hd23b, hd68a, htr237a, htr378a, htr689a, htr789a]
        ·
          have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
            linarith only [hlam, htr1310c, htr135b, htr1510b])
          obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
            linarith only [hlam, htr1310c, htr136b, htr1610b])
          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
            linarith only [hlam, htr1310c, htr137b, htr1710b])
          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
          have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
            linarith only [hlam, htr135c, htr1510a, htr3510a])
          obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc5610yx, htr1310a, htr135a, htr3510b, htr356a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr136c, htr1610a, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710yx, htr1310a, htr136a, htr3610b, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr137c, htr1710a, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hd23b, hd56a, htr1310a, htr135a, htr235a, htr3610b, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd23b, hd610a, htr236a, htr367a, htr5610a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hd23b, hd67a, htr1310a, htr135a, htr235a, htr3710b, htr6710a]
          ·
            linarith only [hlam, hd23b, hd710a, htr235a, htr356a, htr567a, htr6710a]
      ·
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr135b, htr139c, htr159b])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, htr136b, htr139c, htr169b])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, htr137b, htr139c, htr179b])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, htr135c, htr159a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc569yx, htr135a, htr139a, htr356a, htr359b])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr136c, htr169a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679yx, htr136a, htr139a, htr367a, htr369b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr137c, htr179a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd23b, hd56a, htr135a, htr139a, htr235a, htr369b, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd23b, hd69a, htr236a, htr367a, htr567a, htr569a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hd23b, hd67a, htr135a, htr139a, htr235a, htr379b, htr679a]
        ·
          linarith only [hlam, hd23b, hd79a, htr235a, htr356a, htr567a, htr679a]
    ·
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr135b, htr138c, htr158b])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr136b, htr138c, htr168b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr137b, htr138c, htr178b])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr135c, htr158a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hc568yx, htr135a, htr138a, htr356a, htr358b])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr136c, htr168a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678yx, htr136a, htr138a, htr367a, htr368b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr137c, htr178a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd23b, hd56a, htr135a, htr138a, htr235a, htr368b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd23b, hd68a, htr236a, htr367a, htr567a, htr568a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd23b, hd67a, htr135a, htr138a, htr235a, htr378b, htr678a]
      ·
        linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a]
  ·
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr135b, htr137c, htr157b])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr136b, htr137c, htr167b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr135c, htr157a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc567yx, htr135a, htr137a, htr356a, htr357b])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr136c, htr167a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678xy, htr136a, htr137a, htr367b, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hc679xy, htr136a, htr137a, htr367b, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hc6710xy, htr136a, htr137a, htr3610a, htr367b])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd23b, hd79a, htr135a, htr137a, htr235a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd23b, hd56a, htr135a, htr137a, htr235a, htr367b, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd23b, hd67a, htr236a, htr368a, htr567a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hd23b, hd67a, htr236a, htr369a, htr567a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
      linarith only [hlam, hd23b, hd67a, htr236a, htr3610a, htr5610a, htr567a])
    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, htr367b, htr378a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd23b, hd89a, htr235a, htr356a, htr568a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd23b, hd910a, htr235a, htr356a, htr569a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
    rcases m.htr 2 4 7 (by decide) (by decide) with
      ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc023xy, hc678yz, htr024a, htr035a, htr247a, htr356a, htr478a, htr568a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc347yz, htr247a, htr248a, htr378a, htr478b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc023xy, hc689yz, htr024a, htr035a, htr248a, htr356a, htr489a, htr569a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc347yz, htr378a, htr478c, htr489a, htr789a]
      ·
        linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr379a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc023xy, hc689yz, htr027a, htr035a, htr278a, htr356a, htr569a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc023xy, hc6910yz, htr027a, htr035a, htr279a, htr356a, htr5610a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_473 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348c : m.d 3 8 < m.d 4 8)
    : False :=
  proof_shard_473 m htr015a htr016a htr017a htr018a htr024a htr027a htr035a htr035b htr045c htr046c htr134a htr135a htr135b htr135c htr136a htr136b htr136c htr145c htr146c htr235a htr236a htr237a htr245a htr246a htr345c htr346c htr347c htr348c

#print axioms shard_473
end Jsp404.NoSatElevenDBMTerminal
