import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_598 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
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
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
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
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr034a, htr035a, htr345b])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr034a, htr036a, htr346b])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr034a, htr037a, htr347b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  rcases m.htr 3 4 8 (by decide) (by decide) with
    ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
  ·
    rcases m.htr 3 4 9 (by decide) (by decide) with
      ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
    ·
      rcases m.htr 3 4 10 (by decide) (by decide) with
        ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
      ·
        rcases m.htr 4 5 6 (by decide) (by decide) with
          ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
        ·
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hc013yx, hc567yx, htr012a, htr034a, htr125a, htr257a, htr345a, htr456a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr234a, htr345a, htr456a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hd23a, hd68b, htr234a, htr345a, htr456a, htr568a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          rcases m.htr 4 5 7 (by decide) (by decide) with
            ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
          ·
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc013yx, hc567zy, htr012a, htr034a, htr126a, htr267a, htr345a, htr457a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr234a, htr345a, htr457a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr234a, htr345a, htr457a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc256yz, htr267a, htr567c, htr578a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc256yz, htr267b, htr278a, htr567a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr458a, htr458b, htr458c, _, _⟩
              linarith only [hlam, hc013yx, hc578zy, htr012a, htr034a, htr127a, htr278a, htr345a, htr458a])
            obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hc256yz, htr267a, htr567c, htr579a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc256yz, htr267b, htr279a, htr567a, htr679a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc013yx, hc789yz, htr012a, htr034a, htr127a, htr279a, htr348a, htr489a])
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
              linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
          ·
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc256yz, htr267a, htr456a, htr457a, htr567b])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd23a, hd56b, htr235a, htr357a, htr456a, htr457a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hc013yx, hc678yz, htr012a, htr034a, htr126a, htr268a, htr347a, htr478a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc013yx, hc789yx, htr012a, htr034a, htr127a, htr279a, htr347a, htr478a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, hc256yz, htr268a, htr345c, htr358a, htr456a, htr568b])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd27a, hd56b, htr279a, htr456a, htr457a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
              linarith only [hlam, hc013yx, hc789zy, htr012a, htr034a, htr128a, htr289a, htr347a, htr479a])
            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hd25a, hd89b, htr257a, htr357a, htr358a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            rcases m.htr 6 8 9 (by decide) (by decide) with
              ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
            ·
              linarith only [hlam, hc256yz, htr268a, htr568c, htr589a, htr689a]
            ·
              linarith only [hlam, hc256yz, htr268b, htr289a, htr568a, htr689a]
        ·
          rcases m.htr 2 5 6 (by decide) (by decide) with
            ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
          ·
            rcases m.htr 3 5 6 (by decide) (by decide) with
              ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, htr035c, htr056a, htr356a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hd23a, hd57b, htr235a, htr356a, htr456a, htr457a])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              rcases m.htr 3 5 7 (by decide) (by decide) with
                ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, htr035c, htr057a, htr357a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, htr235c, htr257a, htr357a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                rcases m.htr 3 5 8 (by decide) (by decide) with
                  ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                ·
                  rcases m.htr 3 5 9 (by decide) (by decide) with
                    ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
                  ·
                    rcases m.htr 3 5 10 (by decide) (by decide) with
                      ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                    ·
                      rcases m.htr 5 6 7 (by decide) (by decide) with
                        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                      ·
                        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                          linarith only [hlam, hc013yx, hc678yx, htr012a, htr034a, htr126a, htr268a, htr345b, htr356a, htr567a])
                        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                          linarith only [hlam, hc245yz, htr256b, htr268a, htr356c, htr368a, htr456a])
                        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                          linarith only [hlam, hd23a, hd67b, htr234a, htr346b, htr368a, htr467a, htr468a])
                        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc013yx, hc678zy, htr012a, htr034a, htr127a, htr278a, htr346a, htr468a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc245yz, htr257b, htr278a, htr457a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        rcases m.htr 6 7 8 (by decide) (by decide) with
                          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a]
                        ·
                          linarith only [hlam, hd23a, hd67b, htr235a, htr357a, htr578a, htr678a]
                      ·
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                          linarith only [hlam, hc013yx, hc678xy, htr012a, htr034a, htr126a, htr267a, htr345b, htr356a, htr568a])
                        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                          linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
                        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc013yx, hc678yz, htr012a, htr034a, htr126a, htr268a, htr347a, htr478a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                          linarith only [hlam, hc013yx, hc467zy, htr012a, htr034a, htr126a, htr267a, htr347b, htr378a, htr478a])
                        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc245yz, htr257b, htr278a, htr357c, htr378a, htr457a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        rcases m.htr 6 7 8 (by decide) (by decide) with
                          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                        ·
                          linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a]
                        ·
                          linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]
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
                      have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                        linarith only [hlam, hc245yz, htr036c, htr0610a, htr256b, htr2610a, htr356c, htr456a])
                      obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                        linarith only [hlam, hc245yz, htr037c, htr0710a, htr257b, htr2710a, htr357c, htr457a])
                      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc013yx, hc6710yx, htr012a, htr034a, htr126a, htr2610a, htr345b, htr356a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                        linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                      rcases m.htr 6 7 10 (by decide) (by decide) with
                        ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      ·
                        linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr2710a, htr6710a]
                      ·
                        linarith only [hlam, hd01b, hd710a, htr012a, htr126a, htr267a, htr6710a]
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
                    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                      linarith only [hlam, hc245yz, htr036c, htr069a, htr256b, htr269a, htr356c, htr456a])
                    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc245yz, htr037c, htr079a, htr257b, htr279a, htr357c, htr457a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc013yx, hc679yx, htr012a, htr034a, htr126a, htr269a, htr345b, htr356a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    rcases m.htr 6 7 9 (by decide) (by decide) with
                      ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                    ·
                      linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr279a, htr679a]
                    ·
                      linarith only [hlam, hd01b, hd79a, htr012a, htr126a, htr267a, htr679a]
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
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc245yz, htr036c, htr068a, htr256b, htr268a, htr356c, htr456a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc245yz, htr037c, htr078a, htr257b, htr278a, htr357c, htr457a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hc013yx, hc678yx, htr012a, htr034a, htr126a, htr268a, htr345b, htr356a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a]
                  ·
                    linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc045yz, htr057a, htr356a, htr357a, htr456a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, htr056b, htr057c, htr067b])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hc245yz, htr257a, htr356a, htr357a, htr456a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hc245yz, htr036c, htr067a, htr256b, htr267a, htr356c, htr456a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc013yx, hc678xy, htr012a, htr034a, htr126a, htr267a, htr345b, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc013yx, hc678yz, htr012a, htr034a, htr126a, htr268a, htr347a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc013yx, hc457zy, htr012a, htr034a, htr125a, htr257a, htr347b, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45b, hd67a, htr356a, htr357c, htr378a, htr456a, htr678a]
                ·
                  linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]
            ·
              rcases m.htr 1 5 6 (by decide) (by decide) with
                ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
              ·
                rcases m.htr 0 5 6 (by decide) (by decide) with
                  ⟨htr056a, htr056b, htr056c, _, _⟩ | ⟨htr056a, htr056b, htr056c, _, _⟩
                ·
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc013yx, hc678yx, htr012a, htr034a, htr126a, htr268a, htr346a, htr467a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                      linarith only [hlam, hc013yx, hc679yx, htr012a, htr034a, htr126a, htr269a, htr346a, htr467a])
                    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc013yx, hc678zy, htr012a, htr034a, htr127a, htr278a, htr346a, htr468a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr269a, htr456a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr469a, htr569a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc013yx, hc689zy, htr012a, htr034a, htr128a, htr289a, htr346a, htr469a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc267yz, htr278a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc267yz, htr278b, htr289a, htr678a, htr789a]
                  ·
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc013yx, hc678xy, htr012a, htr034a, htr126a, htr267a, htr346a, htr468a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc013yx, hc679xy, htr012a, htr034a, htr126a, htr267a, htr346a, htr469a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc013yx, hc678yz, htr012a, htr034a, htr126a, htr268a, htr347a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr469a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr269a, htr456a, htr569a])
                    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hc013yx, hc689yz, htr012a, htr034a, htr126a, htr269a, htr348a, htr489a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]
                ·
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc013yx, hc678yx, htr012a, htr034a, htr126a, htr268a, htr346a, htr467a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                      linarith only [hlam, hc013yx, hc679yx, htr012a, htr034a, htr126a, htr269a, htr346a, htr467a])
                    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc013yx, hc678zy, htr012a, htr034a, htr127a, htr278a, htr346a, htr468a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr269a, htr456a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr469a, htr569a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc013yx, hc689zy, htr012a, htr034a, htr128a, htr289a, htr346a, htr469a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc267yz, htr278a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc267yz, htr278b, htr289a, htr678a, htr789a]
                  ·
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc013yx, hc678xy, htr012a, htr034a, htr126a, htr267a, htr346a, htr468a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc013yx, hc679xy, htr012a, htr034a, htr126a, htr267a, htr346a, htr469a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr268a, htr456a, htr568a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc013yx, hc678yz, htr012a, htr034a, htr126a, htr268a, htr347a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr469a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                      linarith only [hlam, hc245yz, htr256b, htr269a, htr456a, htr569a])
                    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hc013yx, hc689yz, htr012a, htr034a, htr126a, htr269a, htr348a, htr489a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]
              ·
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, htr015b, htr056a, htr156a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hd01b, hd57a, htr015a, htr156a, htr256a, htr257a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                rcases m.htr 4 5 7 (by decide) (by decide) with
                  ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, htr035c, htr057a, htr345c, htr457a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, htr056c, htr057b, htr067c])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, htr135c, htr157a, htr345c, htr457a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                    linarith only [hlam, hc245yz, htr016b, htr067a, htr156b, htr256a, htr456c, htr467a])
                  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc013yx, hc678yx, htr015a, htr034a, htr156a, htr346a, htr467a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc013yx, hc678zy, htr012a, htr034a, htr127a, htr278a, htr346a, htr468a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc013yx, hc257yz, htr017a, htr034a, htr178a, htr278a, htr345a, htr457a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a]
                  ·
                    linarith only [hlam, hd25a, hd67b, htr156a, htr157b, htr178a, htr256a, htr678a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc245yz, htr015b, htr057a, htr156a, htr256a, htr457a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc245yz, htr156a, htr157a, htr256a, htr457a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  rcases m.htr 4 5 8 (by decide) (by decide) with
                    ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, htr035c, htr058a, htr345c, htr458a])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, htr056c, htr058b, htr068c])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, htr057c, htr058b, htr078c])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc245yz, htr016b, htr068a, htr156b, htr256a, htr456c, htr468a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc245yz, htr057b, htr078a, htr257a, htr457c, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc013yx, hc678xy, htr015a, htr034a, htr156a, htr346a, htr468a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a]
                    ·
                      linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr478a, htr678a]
                  ·
                    rcases m.htr 4 5 9 (by decide) (by decide) with
                      ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                    ·
                      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                        linarith only [hlam, htr035c, htr059a, htr345c, htr459a])
                      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                        linarith only [hlam, htr056c, htr059b, htr069c])
                      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr057c, htr059b, htr079c])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc245yz, htr016b, htr069a, htr156b, htr256a, htr456c, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hc245yz, htr057b, htr079a, htr257a, htr457c, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc013yx, hc679xy, htr015a, htr034a, htr156a, htr346a, htr469a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                        linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                      rcases m.htr 6 7 9 (by decide) (by decide) with
                        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                      ·
                        linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a]
                      ·
                        linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr479a, htr679a]
                    ·
                      rcases m.htr 4 5 10 (by decide) (by decide) with
                        ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                      ·
                        have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                          linarith only [hlam, htr035c, htr0510a, htr345c, htr4510a])
                        obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                          linarith only [hlam, htr0510b, htr056c, htr0610c])
                        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr0510b, htr057c, htr0710c])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                          linarith only [hlam, hc245yz, htr016b, htr0610a, htr156b, htr256a, htr456c, htr4610a])
                        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                          linarith only [hlam, hc245yz, htr057b, htr0710a, htr257a, htr457c, htr4710a])
                        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc013yx, hc6710xy, htr015a, htr034a, htr156a, htr346a, htr4610a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        rcases m.htr 6 7 10 (by decide) (by decide) with
                          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd710b, htr234a, htr346a, htr467a, htr6710a]
                        ·
                          linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr4710a, htr6710a]
                      ·
                        rcases m.htr 5 6 7 (by decide) (by decide) with
                          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                        ·
                          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                            linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
                          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                            linarith only [hlam, hc013yx, hc678yx, htr015a, htr034a, htr156a, htr346a, htr467a, htr568a])
                          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                            linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
                          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hc013yx, hc678zy, htr012a, htr034a, htr127a, htr278a, htr346a, htr468a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                            linarith only [hlam, hc013yx, hc267yz, htr017a, htr034a, htr178a, htr278a, htr346a, htr467a])
                          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc245yz, htr157b, htr178a, htr257a, htr457c, htr478a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          rcases m.htr 6 7 8 (by decide) (by decide) with
                            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                          ·
                            linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a]
                          ·
                            linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr478a, htr678a]
                        ·
                          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                            linarith only [hlam, hc245yz, htr256b, htr267a, htr456a, htr567a])
                          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                            linarith only [hlam, hc013yx, hc678xy, htr015a, htr034a, htr156a, htr346a, htr468a, htr567a])
                          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, hc245yz, htr156b, htr168a, htr256a, htr456c, htr468a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                            linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr267a, htr268a])
                          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc013yx, hc678yz, htr012a, htr034a, htr126a, htr268a, htr347a, htr478a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          rcases m.htr 6 7 8 (by decide) (by decide) with
                            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                          ·
                            linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr578a, htr678a]
                          ·
                            linarith only [hlam, hd01b, hd78a, htr015a, htr156a, htr567a, htr678a]
          ·
            have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr457a, htr457b, htr457c, _, _⟩
              linarith only [hlam, hc013yx, hc567xy, htr012a, htr034a, htr125a, htr256a, htr345a, htr457a])
            obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hc013yx, hc567yz, htr012a, htr034a, htr125a, htr257a, htr346a, htr467a])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr256a, htr257a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd56a, hd67b, htr256a, htr257a, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc013yx, hc678zy, htr012a, htr034a, htr127a, htr278a, htr346a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hc456zy, htr125b, htr158a, htr256a, htr468a, htr568c])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc789xy, htr157a, htr158a, htr578b, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc567xy, htr256a, htr257b, htr279a, htr579a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc013yx, hc789yz, htr012a, htr034a, htr127a, htr279a, htr348a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hd45b, hd89a, htr157a, htr158a, htr457a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 6 8 9 (by decide) (by decide) with
                ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
              ·
                linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a]
              ·
                linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a]
            ·
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hc456zy, htr256a, htr257a, htr467a, htr567c])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                linarith only [hlam, hc013yx, hc578yz, htr012a, htr034a, htr125a, htr258a, htr347a, htr478a])
              obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc013yx, hc789zy, htr012a, htr034a, htr128a, htr289a, htr347a, htr479a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568xy, htr256a, htr258b, htr289a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
              ·
                linarith only [hlam, hd56a, hd78b, htr256a, htr258a, htr589a, htr789a]
      ·
        have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
          linarith only [hlam, htr3410c, htr345b, htr3510b])
        obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
        have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
          linarith only [hlam, htr3410c, htr346b, htr3610b])
        obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, htr3410c, htr347b, htr3710b])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
          linarith only [hlam, htr345c, htr3510a, htr4510a])
        obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
        have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
          linarith only [hlam, hc245yz, htr2510a, htr3410a, htr345a, htr4510b])
        obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc5610yx, htr3410a, htr345a, htr4510b, htr456a])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
          linarith only [hlam, htr346c, htr3610a, htr4610a])
        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
        have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
          linarith only [hlam, hc246yz, htr2610a, htr3410a, htr346a, htr4610b])
        obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc6710yx, htr3410a, htr346a, htr4610b, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, htr347c, htr3710a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
          linarith only [hlam, hc456zy, htr3410a, htr346a, htr4610b, htr5610a])
        obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hd01b, hd610a, htr012a, htr125a, htr256a, htr5610a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd46b, hd510a, htr2510a, htr256a, htr467a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hd45b, hd610a, htr2610a, htr267a, htr456a, htr567a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        rcases m.htr 6 7 10 (by decide) (by decide) with
          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        ·
          linarith only [hlam, hc467zy, htr3410a, htr347a, htr4710b, htr6710a]
        ·
          linarith only [hlam, hd01b, hd710a, htr012a, htr126a, htr267a, htr6710a]
    ·
      have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr359a, htr359b, htr359c, _, _⟩
        linarith only [hlam, htr345b, htr349c, htr359b])
      obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, htr346b, htr349c, htr369b])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, htr347b, htr349c, htr379b])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, htr345c, htr359a, htr459a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, hc245yz, htr259a, htr345a, htr349a, htr459b])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc569yx, htr345a, htr349a, htr456a, htr459b])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, htr346c, htr369a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hc246yz, htr269a, htr346a, htr349a, htr469b])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc679yx, htr346a, htr349a, htr467a, htr469b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, htr347c, htr379a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc456zy, htr346a, htr349a, htr469b, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hd01b, hd69a, htr012a, htr125a, htr256a, htr569a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd46b, hd59a, htr256a, htr259a, htr467a, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd45b, hd69a, htr267a, htr269a, htr456a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        linarith only [hlam, hc467zy, htr347a, htr349a, htr479b, htr679a]
      ·
        linarith only [hlam, hd01b, hd79a, htr012a, htr126a, htr267a, htr679a]
  ·
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, htr345b, htr348c, htr358b])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, htr346b, htr348c, htr368b])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, htr347b, htr348c, htr378b])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, htr345c, htr358a, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc245yz, htr258a, htr345a, htr348a, htr458b])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc568yx, htr345a, htr348a, htr456a, htr458b])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr346c, htr368a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc246yz, htr268a, htr346a, htr348a, htr468b])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc678yx, htr346a, htr348a, htr467a, htr468b])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr347c, htr378a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc456zy, htr346a, htr348a, htr468b, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd46b, hd58a, htr256a, htr258a, htr467a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd45b, hd68a, htr267a, htr268a, htr456a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hc467zy, htr347a, htr348a, htr478b, htr678a]
    ·
      linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]

theorem shard_598 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    : False :=
  proof_shard_598 m htr012a htr015a htr015b htr016a htr016b htr017a htr034a htr125a htr125b htr126a htr127a htr128a htr135c htr234a htr235a htr235c htr345a htr345b htr345c htr346a htr346b htr346c htr347a htr347b htr347c

#print axioms shard_598
end Jsp404.NoSatElevenDBMTerminal
