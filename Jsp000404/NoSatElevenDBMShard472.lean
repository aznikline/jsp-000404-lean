import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_472 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
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
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc018xy, hc018yx, hc018yz, hc018zy⟩ := endpoint_caps m 0 1 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc345xy, htr035a, htr036a, htr134a, htr136a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc345xy, htr034c, htr035a, htr047a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hc345xy, htr034c, htr035a, htr048a, htr348a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  rcases m.htr 1 3 7 (by decide) (by decide) with
    ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc345xy, htr035a, htr037a, htr134a, htr137a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, hc234zy, htr134a, htr137a, htr247a, htr347c])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 1 3 8 (by decide) (by decide) with
      ⟨htr138a, htr138b, htr138c, _, _⟩ | ⟨htr138a, htr138b, htr138c, _, _⟩
    ·
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
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc346xy, htr134a, htr136b, htr167a, htr367a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd34a, hd68b, htr134a, htr135a, htr356a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hd34a, hd56b, htr134a, htr136a, htr368a, htr568a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc346xy, htr134a, htr136b, htr168a, htr368a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
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
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd34a, hd79b, htr134a, htr135a, htr345c, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr134a, htr137a, htr379a, htr579a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc347xy, htr134a, htr137b, htr179a, htr379a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc012yx, hc567zy, htr017a, htr024a, htr178a, htr245a, htr457a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                linarith only [hlam, hc012yx, hc578zy, htr016a, htr024a, htr167a, htr245a, htr458a, htr678a])
              obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc012yx, hc567zy, htr017a, htr024a, htr179a, htr245a, htr457a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc012yx, hc789yz, htr016a, htr024a, htr167a, htr248a, htr489a, htr679a])
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
                linarith only [hlam, hd34a, hd56b, htr015b, htr057a, htr134a, htr135b, htr456a, htr457a])
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
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr017b, htr078a, htr134a, htr137b, htr247c, htr278a, htr456a, htr457c])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr134a, htr137a, htr237b, htr278a, htr456a, htr457c, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc012yx, hc789yx, htr015a, htr024a, htr157a, htr247a, htr478a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc567yx, htr247c, htr279a, htr456a, htr457c, htr579a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr134a, htr137a, htr237b, htr279a, htr456a, htr457c, htr479a])
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
                  linarith only [hlam, hc012yx, hc789zy, htr016a, htr024a, htr168a, htr247a, htr479a, htr689a]
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc567yx, htr057a, htr058a, htr456a, htr458a])
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
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hd34a, hd56b, htr017b, htr079a, htr134a, htr137b, htr247c, htr279a, htr456a, htr457c])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hd34a, hd56b, htr018b, htr089a, htr134a, htr138b, htr248c, htr289a, htr456a, htr458c])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hd34a, hd56b, htr134a, htr137a, htr237b, htr279a, htr456a, htr457c, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc012yx, hc789xy, htr015a, htr024a, htr157a, htr247a, htr479a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc567yx, htr247c, htr278a, htr456a, htr457c, htr578a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd34a, hd89b, htr134a, htr137a, htr237b, htr278a, htr789a]
                  ·
                    linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr238b, htr289a, htr789a]
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
                    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                      linarith only [hlam, hd34a, hd56b, htr017b, htr0710a, htr134a, htr137b, htr247c, htr2710a, htr456a, htr457c])
                    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hd34a, hd56b, htr018b, htr0810a, htr134a, htr138b, htr248c, htr2810a, htr456a, htr458c])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                      linarith only [hlam, hd34a, hd56b, htr134a, htr137a, htr237b, htr2710a, htr456a, htr457c, htr4710a])
                    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hc012yx, hc7810xy, htr015a, htr024a, htr157a, htr247a, htr4710a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc567yx, htr247c, htr278a, htr456a, htr457c, htr578a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd34a, hd810b, htr134a, htr137a, htr237b, htr278a, htr7810a]
                    ·
                      linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr238b, htr2810a, htr7810a]
                  ·
                    rcases m.htr 4 7 8 (by decide) (by decide) with
                      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                    ·
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc012yx, hc789yx, htr015a, htr024a, htr157a, htr247a, htr478a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc567yx, htr247c, htr279a, htr456a, htr457c, htr579a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd34a, hd56b, htr134a, htr137a, htr237b, htr279a, htr456a, htr457c, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hc568yx, htr248c, htr289a, htr456a, htr458c, htr589a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd89b, htr134a, htr137a, htr347c, htr478a, htr789a]
                      ·
                        linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr238b, htr289a, htr789a]
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
              linarith only [hlam, hc345xy, htr015b, htr056a, htr134a, htr135b, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc345xy, htr134a, htr135b, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, htr235b, htr256a, htr356a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, htr345c, htr356a, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            rcases m.htr 3 5 7 (by decide) (by decide) with
              ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, htr035c, htr057a, htr357a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr056c, htr057b, htr067c])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, htr135c, htr157a, htr357a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hd25b, hd34a, htr134a, htr135a, htr257a, htr357a])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr016b, htr067a, htr134a, htr136b, htr256c, htr257a, htr267a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hd34a, hd45b, htr134a, htr135a, htr357a, htr457a])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr134a, htr136a, htr236b, htr267a, htr456c, htr457a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc012yx, hc678yx, htr015a, htr024a, htr156a, htr246a, htr467a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc567xy, htr256c, htr257a, htr268a, htr568a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr134a, htr136a, htr236b, htr268a, htr456c, htr457a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc012yx, hc679yx, htr015a, htr024a, htr156a, htr246a, htr467a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc567xy, htr256c, htr257a, htr269a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hd34a, hd57b, htr134a, htr136a, htr236b, htr269a, htr456c, htr457a, htr469a])
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
                linarith only [hlam, hd34a, hd89b, htr134a, htr136a, htr236b, htr268a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr134a, htr138a, htr389a, htr689a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc348xy, htr134a, htr138b, htr189a, htr389a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc012yx, hc678zy, htr018a, htr024a, htr189a, htr246a, htr468a, htr789a]
              ·
                linarith only [hlam, hc012yx, hc689zy, htr017a, htr024a, htr178a, htr246a, htr469a, htr789a]
            ·
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc345xy, htr134a, htr135b, htr157a, htr357a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, htr036c, htr067a, htr367a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
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
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc012yx, hc567yz, htr017a, htr024a, htr178a, htr246a, htr467a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc012yx, hc678zy, htr015a, htr024a, htr157a, htr246a, htr468a, htr578a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr016b, htr068a, htr134a, htr136b, htr467a, htr468a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc012yx, hc789xy, htr015a, htr024a, htr157a, htr247a, htr479a, htr578a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hc678yx, htr067b, htr068a, htr079a, htr467c, htr479a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd23b, hd78a, htr037c, htr079a, htr237a, htr578a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc012yx, hc789yz, htr015a, htr024a, htr157a, htr248a, htr489a, htr579a])
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
                  linarith only [hlam, hc346xy, htr016b, htr067a, htr134a, htr136b, htr367a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc346xy, htr134a, htr136b, htr167a, htr367a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, htr236b, htr267a, htr367a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, htr346c, htr367a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                rcases m.htr 5 6 7 (by decide) (by decide) with
                  ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                ·
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hd23b, hd56a, htr035c, htr058a, htr156c, htr158a, htr167a, htr235a, htr567a])
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
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc256zy, htr067b, htr078a, htr267c, htr278a, htr567a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd34a, hd68b, htr134a, htr137a, htr237b, htr278a, htr467c, htr468a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hc012yx, hc789yx, htr016a, htr024a, htr167a, htr247a, htr478a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc256zy, htr267c, htr279a, htr567a, htr679a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hd34a, hd68b, htr134a, htr137a, htr237b, htr279a, htr467c, htr468a, htr479a])
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
                      linarith only [hlam, hd34a, hd89b, htr134a, htr137a, htr237b, htr278a, htr789a]
                    ·
                      linarith only [hlam, hd56a, hd78b, htr167a, htr168b, htr189a, htr567a, htr789a]
                  ·
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, hc456zy, htr016b, htr068a, htr167a, htr468a, htr567a])
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
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc256zy, htr067b, htr079a, htr267c, htr279a, htr567a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hc456zy, htr068b, htr089a, htr248c, htr289a, htr468c, htr568a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd34a, hd69b, htr134a, htr137a, htr237b, htr279a, htr467c, htr469a, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc012yx, hc789xy, htr016a, htr024a, htr167a, htr247a, htr479a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd89b, htr134a, htr137a, htr237b, htr278a, htr789a]
                      ·
                        linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr238b, htr289a, htr789a]
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
                        have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                          linarith only [hlam, hc256zy, htr067b, htr0710a, htr267c, htr2710a, htr567a])
                        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hc456zy, htr068b, htr0810a, htr248c, htr2810a, htr468c, htr568a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                          linarith only [hlam, hd34a, hd610b, htr134a, htr137a, htr237b, htr2710a, htr4610a, htr467c, htr4710a])
                        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hc012yx, hc7810xy, htr016a, htr024a, htr167a, htr247a, htr4710a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        rcases m.htr 7 8 10 (by decide) (by decide) with
                          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        ·
                          linarith only [hlam, hd34a, hd810b, htr134a, htr137a, htr237b, htr278a, htr7810a]
                        ·
                          linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr238b, htr2810a, htr7810a]
                      ·
                        rcases m.htr 6 7 8 (by decide) (by decide) with
                          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                        ·
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc012yx, hc789yx, htr016a, htr024a, htr167a, htr247a, htr478a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hc256zy, htr267c, htr279a, htr567a, htr679a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hd34a, hd78b, htr134a, htr137a, htr237b, htr279a, htr478a, htr479a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc012yx, hc578yz, htr018a, htr024a, htr189a, htr247a, htr478a, htr589a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hc456zy, htr168b, htr189a, htr248c, htr289a, htr468c, htr568a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd34a, hd89b, htr134a, htr137a, htr237b, htr278a, htr789a]
                          ·
                            linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr238b, htr289a, htr789a]
                        ·
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hc012yx, hc789xy, htr016a, htr024a, htr167a, htr247a, htr479a, htr678a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                            linarith only [hlam, hc456zy, htr067b, htr079a, htr467c, htr479a, htr567a])
                          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hd23b, hd57a, htr236a, htr367a, htr578a, htr678a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                            linarith only [hlam, hd23b, hd78a, htr037c, htr079a, htr237a, htr578a, htr579a])
                          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                            linarith only [hlam, hc012yx, hc789yz, htr015a, htr024a, htr157a, htr248a, htr489a, htr579a])
                          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
                          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd23b, hd78a, htr036c, htr068a, htr236a, htr689a, htr789a]
                          ·
                            linarith only [hlam, hd23b, hd89a, htr236a, htr367a, htr678a, htr789a]
                ·
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc012yx, hc678xy, htr015a, htr024a, htr156a, htr246a, htr468a, htr567a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hd34a, hd46b, htr134a, htr136a, htr368a, htr468a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                    linarith only [hlam, hc012yx, hc679xy, htr015a, htr024a, htr156a, htr246a, htr469a, htr567a])
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
                    linarith only [hlam, hc012yx, hc678yz, htr015a, htr024a, htr156a, htr247a, htr478a, htr568a])
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
                    linarith only [hlam, hc012yx, hc689yz, htr015a, htr024a, htr156a, htr248a, htr489a, htr569a])
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
          have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
            linarith only [hlam, htr013b, htr0310a, htr1310a])
          obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, htr0310c, htr035b, htr0510b])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, htr0310c, htr036b, htr0610b])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0310c, htr037b, htr0710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
            linarith only [hlam, htr035c, htr0510a, htr3510a])
          obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc5610yx, htr013b, htr035a, htr1310a, htr3510b, htr356a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr036c, htr0610a, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710yx, htr013b, htr036a, htr1310a, htr3610b, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr037c, htr0710a, htr3710a])
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
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, htr013b, htr039a, htr139a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr035b, htr039c, htr059b])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, htr036b, htr039c, htr069b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr037b, htr039c, htr079b])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, htr035c, htr059a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc569yx, htr013b, htr035a, htr139a, htr356a, htr359b])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr036c, htr069a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679yx, htr013b, htr036a, htr139a, htr367a, htr369b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr037c, htr079a, htr379a])
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
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr013b, htr038a, htr138a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035b, htr038c, htr058b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr036b, htr038c, htr068b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr037b, htr038c, htr078b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr035c, htr058a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hc568yx, htr013b, htr035a, htr138a, htr356a, htr358b])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr036c, htr068a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678yx, htr013b, htr036a, htr138a, htr367a, htr368b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr037c, htr078a, htr378a])
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
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr013b, htr037a, htr137a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr035b, htr037c, htr057b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr036b, htr037c, htr067b])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr035c, htr057a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc567yx, htr013b, htr035a, htr137a, htr356a, htr357b])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc345xy, htr134a, htr135b, htr156a, htr356a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr036c, htr067a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678xy, htr013b, htr036a, htr137a, htr367b, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hc679xy, htr013b, htr036a, htr137a, htr367b, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hc6710xy, htr013b, htr036a, htr137a, htr3610a, htr367b])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc357yx, htr035a, htr037c, htr078a, htr378a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
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
    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
      linarith only [hlam, hd23b, hd810a, htr235a, htr356a, htr568a, htr6810a])
    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc012yx, hc689yz, htr015a, htr027a, htr156a, htr278a, htr569a, htr789a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
        linarith only [hlam, hc267zy, htr078c, htr0810a, htr278a, htr678b, htr6810a])
      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hc017yx, hc268zy, htr015a, htr078a, htr156a, htr289a, htr568a, htr789a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hc018yx, hc689yz, htr015a, htr0810a, htr156a, htr2810a, htr289a, htr569a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc014yx, hc689yz, htr015a, htr047a, htr156a, htr478a, htr569a, htr789a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr378a, htr478a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc014yx, hc467zy, htr015a, htr048a, htr156a, htr247a, htr248a, htr567a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      rcases m.htr 4 8 10 (by decide) (by decide) with
        ⟨htr4810a, htr4810b, htr4810c, _, _⟩ | ⟨htr4810a, htr4810b, htr4810c, _, _⟩
      ·
        linarith only [hlam, hc012yx, hc6810yz, htr015a, htr024a, htr156a, htr248a, htr4810a, htr5610a]
      ·
        linarith only [hlam, hc012yx, hc468zy, htr015a, htr028a, htr156a, htr2810a, htr4810a, htr568a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc012yx, hc678yz, htr015a, htr024a, htr156a, htr247a, htr478a, htr568a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc014yx, hc468zy, htr015a, htr047a, htr156a, htr247a, htr248a, htr568a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      rcases m.htr 4 8 9 (by decide) (by decide) with
        ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
      ·
        linarith only [hlam, hc014yx, hc678yz, htr015a, htr048a, htr156a, htr489a, htr568a, htr789a]
      ·
        linarith only [hlam, hd45b, hd68a, htr245a, htr248a, htr489a, htr689a]

theorem shard_472 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    : False :=
  proof_shard_472 m htr013b htr015a htr015b htr016a htr016b htr017a htr017b htr018a htr018b htr024a htr027a htr028a htr034c htr035a htr035b htr035c htr045c htr046c htr134a htr135a htr135b htr135c htr136a htr136b htr145c htr146c htr235a htr235b htr236a htr236b htr237a htr237b htr238b htr245a htr246a htr345c htr346c htr347a htr347c htr348a htr348c

#print axioms shard_472
end Jsp404.NoSatElevenDBMTerminal
