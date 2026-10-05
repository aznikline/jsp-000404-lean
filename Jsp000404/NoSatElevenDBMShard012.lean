import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_012 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr458a : m.d 5 8 + lam ≤ m.d 4 5)
    (htr458b : m.d 5 8 < m.d 4 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc4910xy, hc4910yx, hc4910yz, hc4910zy⟩ := endpoint_caps m 4 9 10 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd01a, hd67b, htr012a, htr124a, htr246a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd01a, hd46b, htr012a, htr126a, htr267a, htr467a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd01a, hd68b, htr012a, htr124a, htr246a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd01a, hd46b, htr012a, htr126a, htr268a, htr468a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd01a, hd69b, htr012a, htr124a, htr246a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd01a, hd46b, htr012a, htr126a, htr269a, htr469a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hd01a, hd610b, htr012a, htr124a, htr246a, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  rcases m.htr 2 4 7 (by decide) (by decide) with
    ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
  ·
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd01a, hd78b, htr012a, htr124a, htr247a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd01a, hd79b, htr012a, htr124a, htr247a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd01a, hd47b, htr012a, htr127a, htr279a, htr479a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
      linarith only [hlam, hd01a, hd710b, htr012a, htr124a, htr247a, htr4710a])
    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
    rcases m.htr 2 4 8 (by decide) (by decide) with
      ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
    ·
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr012a, htr124a, htr248a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd01a, hd810b, htr012a, htr124a, htr248a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      rcases m.htr 2 4 9 (by decide) (by decide) with
        ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
      ·
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd01a, hd910b, htr012a, htr124a, htr249a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 2 4 10 (by decide) (by decide) with
          ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc456zy, htr056a, htr057a, htr467a, htr567c])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc456zy, htr357b, htr378a, htr467a, htr567b, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hc013xy, hc478zy, htr012a, htr035a, htr124a, htr248a, htr357a, htr578a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23b, hd78a, htr035a, htr037a, htr235a, htr378a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc023yz, htr037a, htr235c, htr257c, htr279a, htr379a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd23b, hd78a, htr237a, htr379a, htr578a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc015xy, hc489zy, htr012a, htr057a, htr124a, htr249a, htr578a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc015xy, hc4910zy, htr012a, htr057a, htr124a, htr2410a, htr579a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
            ·
              linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a]
          ·
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc467zy, htr367a, htr368a, htr478a, htr678c])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc467zy, htr368b, htr389a, htr478a, htr678b, htr789a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc013xy, hc489zy, htr012a, htr036a, htr124a, htr249a, htr368a, htr689a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hd23b, hd89a, htr036a, htr038a, htr236a, htr389a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hd23b, hd89a, htr235a, htr356a, htr568a, htr689a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              rcases m.htr 0 3 5 (by decide) (by decide) with
                ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
              ·
                linarith only [hlam, hc023yz, htr035a, htr235c, htr256a, htr356a]
              ·
                linarith only [hlam, hc345yz, htr035a, htr038a, htr356c, htr368c, htr456a]
            ·
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hc023yz, htr035a, htr235c, htr256a, htr356a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc345yz, htr035a, htr036a, htr356c, htr456a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a]
              ·
                linarith only [hlam, hc013xy, hc478zy, htr012a, htr036a, htr124a, htr248a, htr367a, htr678a]
        ·
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc456zy, htr2410a, htr246a, htr4610b, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc457zy, htr2410a, htr247a, htr4710b, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc467zy, htr2410a, htr247a, htr4710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc478zy, htr2410a, htr248a, htr4810b, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd45b, hd610a, htr356a, htr357a, htr457a, htr5610a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd23b, hd810a, htr235a, htr357a, htr578a, htr7810a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a]
            ·
              linarith only [hlam, hd46b, hd710a, htr467a, htr5710a, htr578a, htr678a]
          ·
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd23b, hd710a, htr235a, htr356a, htr567a, htr6710a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd45b, hd710a, htr356a, htr357a, htr456a, htr5710a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd45b, hd710a, htr457a, htr578a, htr6710a, htr678a]
            ·
              linarith only [hlam, hd45b, hd810a, htr456a, htr567a, htr678a, htr7810a]
      ·
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc456zy, htr246a, htr249a, htr469b, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc457zy, htr247a, htr249a, htr479b, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc467zy, htr247a, htr249a, htr479b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc478zy, htr248a, htr249a, htr489b, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hd45b, hd69a, htr356a, htr357a, htr457a, htr569a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr235a, htr357a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a]
          ·
            linarith only [hlam, hd46b, hd79a, htr467a, htr578a, htr579a, htr678a]
        ·
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd23b, hd79a, htr235a, htr356a, htr567a, htr679a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hd45b, hd79a, htr356a, htr357a, htr456a, htr579a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd45b, hd79a, htr457a, htr578a, htr678a, htr679a]
          ·
            linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a]
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc345yz, htr245a, htr248a, htr358a, htr458b])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc346yz, htr246a, htr248a, htr368a, htr468b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc456zy, htr246a, htr248a, htr468b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc457zy, htr247a, htr248a, htr478b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc467zy, htr247a, htr248a, htr478b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd45b, hd68a, htr356a, htr357a, htr457a, htr568a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd23b, hd68a, htr236a, htr367a, htr567a, htr568a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc023yz, htr036a, htr235c, htr256c, htr267a, htr367a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd23b, hd68a, htr035a, htr036a, htr235a, htr368a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd46b, hd78a, htr467a, htr578a, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc013xy, hc789yz, htr012a, htr035a, htr128a, htr289a, htr357a, htr579a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc458yx, htr245a, htr248c, htr289a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd45b, hd78a, htr245a, htr248a, htr489a, htr789a]
        ·
          linarith only [hlam, hd46b, hd89a, htr467a, htr567a, htr568a, htr678b, htr789a]
      ·
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc023yz, htr035a, htr235c, htr256a, htr356a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23b, hd58a, htr035a, htr036a, htr236a, htr358a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd45b, hd78a, htr356a, htr357a, htr456a, htr578a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd45b, hd68a, htr367a, htr368a, htr456a, htr567a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc345yz, htr357a, htr457c, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45b, hd89a, htr356a, htr358a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45b, hd58a, htr245a, htr248a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc458yx, htr245a, htr248c, htr289a, htr489a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hd45b, hd78a, htr457a, htr579a, htr678a, htr679a]
        ·
          linarith only [hlam, hc013xy, hc789yz, htr012a, htr036a, htr128a, htr289a, htr367a, htr679a]
  ·
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc345yz, htr245a, htr247a, htr357a, htr457b])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc346yz, htr246a, htr247a, htr367a, htr467b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc456zy, htr246a, htr247a, htr467b, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
    ·
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc023yz, htr035a, htr235c, htr256a, htr356a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd23b, hd57a, htr035a, htr036a, htr236a, htr357a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr367a, htr368a, htr456a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr367a, htr369a, htr456a, htr569a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr356a, htr357a, htr456a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr478a, htr578a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd45b, hd79a, htr356a, htr357a, htr456a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr479a, htr579a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hd45b, hd710a, htr356a, htr357a, htr456a, htr5710a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr4710a, htr5710a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr2710a, htr4710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc013xy, hc789zy, htr012a, htr036a, htr127a, htr279a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc013xy, hc7910zy, htr012a, htr036a, htr127a, htr2710a, htr369a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd01a, hd910b, htr012a, htr127a, htr279a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr356a, htr358a, htr458a, htr567a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr478a, htr678a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd23b, hd79a, htr235a, htr356a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr479a, htr679a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd01a, hd910b, htr012a, htr127a, htr279a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr236a, htr368a, htr567a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc023yz, htr036a, htr235c, htr256c, htr268a, htr368a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr035a, htr036a, htr235a, htr367a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc013xy, hc789zy, htr012a, htr035a, htr127a, htr279a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a]
        ·
          linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a]
      ·
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc013xy, hc678yz, htr012a, htr035a, htr127a, htr278a, htr356a, htr568a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr035a, htr036a, htr235a, htr367a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc023yz, htr036a, htr235c, htr256c, htr269a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd23b, hd67a, htr236a, htr369a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr235a, htr356a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd23b, hd910a, htr235a, htr356a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_012 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr457a : m.d 5 7 + lam ≤ m.d 4 5)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 4 5)
    (htr458a : m.d 5 8 + lam ≤ m.d 4 5)
    (htr458b : m.d 5 8 < m.d 4 8)
    : False :=
  proof_shard_012 m htr012a htr124a htr126a htr127a htr128a htr235a htr235c htr236a htr237a htr245a htr246a htr256a htr256c htr257c htr456a htr456c htr457a htr457b htr457c htr458a htr458b

#print axioms shard_012
end Jsp404.NoSatElevenDBMTerminal
