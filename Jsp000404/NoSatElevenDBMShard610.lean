import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_610 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr458a : m.d 4 5 + lam ≤ m.d 5 8)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr459c : m.d 4 9 < m.d 5 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < 4*lam := by
    linarith only [hd06braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < 4*lam := by
    linarith only [hd38braw, hp]
  obtain ⟨hd39a, hd39braw⟩ := m.hrange 3 9 (by decide)
  have hd39b : m.d 3 9 < 4*lam := by
    linarith only [hd39braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
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
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
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
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc018xy, hc018yx, hc018yz, hc018zy⟩ := endpoint_caps m 0 1 8 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hc023zy, htr034a, htr234b, htr246a, htr346a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc234yz, htr034a, htr036a, htr246a, htr346b])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457xy, htr245a, htr246a, htr346a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458xy, htr245a, htr246a, htr346a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hc459xy, htr245a, htr246a, htr346a, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  rcases m.htr 2 4 7 (by decide) (by decide) with
    ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc234yz, htr034a, htr037a, htr247a, htr347b])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc456xy, htr146a, htr147a, htr245a, htr247a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc345zy, htr245a, htr247a, htr357a, htr457c])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    rcases m.htr 2 4 8 (by decide) (by decide) with
      ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
    ·
      rcases m.htr 0 4 6 (by decide) (by decide) with
        ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
      ·
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc345yx, htr034b, htr035a, htr046a, htr346a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc456xy, htr046a, htr047a, htr245a, htr247a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd36b, hd45a, htr245a, htr246a, htr367a, htr467a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr467a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc013yx, hc678yx, htr012a, htr035a, htr126a, htr268a, htr356a, htr567a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr245a, htr246b, htr268a, htr367a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr245a, htr246a, htr346b, htr368a, htr567a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc013yx, hc678zy, htr012a, htr035a, htr127a, htr278a, htr356a, htr568a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457xy, htr245a, htr247b, htr278a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd45a, hd78b, htr245a, htr246a, htr467a, htr678a]
              ·
                linarith only [hlam, hd45a, hd67b, htr245a, htr247a, htr478a, htr678a]
            ·
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc013yx, hc678xy, htr012a, htr035a, htr126a, htr267a, htr356a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc456xy, htr245a, htr246b, htr268a, htr468a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc013yx, hc678yz, htr012a, htr035a, htr126a, htr268a, htr357a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd45a, hd57b, htr245a, htr247a, htr478a, htr578a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc457xy, htr245a, htr247b, htr278a, htr478a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a]
              ·
                linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, htr014b, htr0410a, htr124b, htr2410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410c, htr046b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0410c, htr047b, htr0710b])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hc457xy, htr047c, htr0710a, htr245a, htr247b, htr2710a])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, htr046c, htr0610a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710yx, htr124b, htr146a, htr2410a, htr4610b, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr2710a, htr6710a]
            ·
              linarith only [hlam, hd01b, hd710a, htr012a, htr126a, htr267a, htr6710a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, htr014b, htr049a, htr124b, htr249a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046b, htr049c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr047b, htr049c, htr079b])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hc457xy, htr047c, htr079a, htr245a, htr247b, htr279a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, htr046c, htr069a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc679yx, htr124b, htr146a, htr249a, htr467a, htr469b])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr279a, htr679a]
          ·
            linarith only [hlam, hd01b, hd79a, htr012a, htr126a, htr267a, htr679a]
      ·
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hd06b, hd45a, htr067a, htr245a, htr246a, htr467a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd36b, hd45a, htr245a, htr246a, htr367a, htr467a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hd23a, hd67b, htr035a, htr036a, htr235a, htr367a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr467a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc013yx, hc678yx, htr012a, htr035a, htr126a, htr268a, htr356a, htr567a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr067a, htr068a, htr245a, htr246b, htr268a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr046b, htr068a, htr245a, htr246a, htr567a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc013yx, hc678zy, htr012a, htr035a, htr127a, htr278a, htr356a, htr568a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457xy, htr245a, htr247b, htr278a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd45a, hd78b, htr245a, htr246a, htr467a, htr678a]
              ·
                linarith only [hlam, hd45a, hd67b, htr245a, htr247a, htr478a, htr678a]
            ·
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, htr456c, htr467a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457xy, htr245a, htr247b, htr278a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd37b, hd45a, htr245a, htr247a, htr378a, htr478a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr035a, htr037a, htr235a, htr378a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc013yx, hc678xy, htr012a, htr035a, htr126a, htr267a, htr357a, htr567c, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc456xy, htr245a, htr246b, htr268a, htr468a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                linarith only [hlam, hc013yx, hc678yz, htr012a, htr035a, htr126a, htr268a, htr357a, htr578a]
              ·
                linarith only [hlam, hd45a, hd57b, htr245a, htr247a, htr478a, htr578a]
          ·
            have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
              linarith only [hlam, htr124b, htr1410a, htr2410a])
            obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
            have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
              linarith only [hlam, htr1410c, htr146b, htr1610b])
            obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
            have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
              linarith only [hlam, htr1410c, htr147b, htr1710b])
            obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hd01b, hd45a, htr017a, htr1710a, htr245a, htr247b, htr2710a])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, htr146c, htr1610a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710yx, htr124b, htr146a, htr2410a, htr4610b, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr2710a, htr6710a]
            ·
              linarith only [hlam, hd01b, hd710a, htr012a, htr126a, htr267a, htr6710a]
        ·
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, htr124b, htr149a, htr249a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, htr146b, htr149c, htr169b])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, htr147b, htr149c, htr179b])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hd01b, hd45a, htr017a, htr179a, htr245a, htr247b, htr279a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, htr146c, htr169a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc679yx, htr124b, htr146a, htr249a, htr467a, htr469b])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr279a, htr679a]
          ·
            linarith only [hlam, hd01b, hd79a, htr012a, htr126a, htr267a, htr679a]
    ·
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr124b, htr148a, htr248a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr146b, htr148c, htr168b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr147b, htr148c, htr178b])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd01b, hd45a, htr017a, htr178a, htr245a, htr247b, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr146c, htr168a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc678yx, htr124b, htr146a, htr248a, htr467a, htr468b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a]
      ·
        linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, htr014b, htr047a, htr124b, htr247a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr124b, htr147a, htr247a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr146b, htr147c, htr167b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr146c, htr167a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc678xy, htr124b, htr146a, htr247a, htr467b, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc456xy, htr245a, htr246b, htr268a, htr468a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hc679xy, htr124b, htr146a, htr247a, htr467b, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hc456xy, htr245a, htr246b, htr269a, htr469a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hc6710xy, htr124b, htr146a, htr247a, htr4610a, htr467b])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, hc456xy, htr245a, htr246b, htr2610a, htr4610a])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr124a, htr247a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr124a, htr247a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
      linarith only [hlam, hd01b, hd710a, htr012a, htr124a, htr247a, htr4710a])
    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, htr467b, htr478a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, htr467b, htr479a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr289a, htr689a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
      linarith only [hlam, hd01b, hd810a, htr012a, htr126a, htr268a, htr6810a])
    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr2810a, htr6810a])
    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd01b, hd910a, htr012a, htr126a, htr269a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
      linarith only [hlam, hd01b, hd69a, htr012a, htr129a, htr2910a, htr6910a])
    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
    rcases m.htr 2 4 8 (by decide) (by decide) with
      ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc234yz, htr034a, htr038a, htr248a, htr348b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc345zy, htr245a, htr248a, htr358a, htr458c])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc458xy, htr245a, htr248b, htr289a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd38b, hd45a, htr245a, htr248a, htr389a, htr489a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd23a, hd89b, htr035a, htr038a, htr235a, htr389a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      rcases m.htr 5 8 9 (by decide) (by decide) with
        ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
      ·
        linarith only [hlam, hc013yx, hc689yz, htr012a, htr035a, htr126a, htr269a, htr358a, htr589a]
      ·
        linarith only [hlam, hd45a, hd58b, htr245a, htr248a, htr489a, htr589a]
    ·
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr124b, htr248a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, htr248b, htr2810a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      rcases m.htr 0 4 6 (by decide) (by decide) with
        ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
      ·
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc345yx, htr034b, htr035a, htr046a, htr346a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc348yx, htr034b, htr038a, htr046a, htr346a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc456xy, htr045c, htr046a, htr057a, htr457a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc456xy, htr045c, htr046a, htr058a, htr458a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hd34b, hd68a, htr046a, htr048c, htr089a, htr346a, htr689a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, hd34b, hd68a, htr046a, htr048c, htr0810a, htr346a, htr6810a])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc017yx, hc368zy, htr012a, htr078a, htr126a, htr268a, htr389a, htr789a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hc018yx, hc689yz, htr012a, htr0810a, htr126a, htr269a, htr3810a, htr389a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc015yx, hc689yz, htr012a, htr057a, htr126a, htr269a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc345zy, htr357a, htr457b, htr478a, htr578a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc015yx, hc457yz, htr012a, htr058a, htr124a, htr247a, htr357a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc013yx, hc6810yz, htr012a, htr035a, htr126a, htr2610a, htr358a, htr5810a]
          ·
            linarith only [hlam, hc013yx, hc568zy, htr012a, htr038a, htr126a, htr268a, htr3810a, htr5810a]
        ·
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc013yx, hc678yz, htr012a, htr038a, htr126a, htr268a, htr389a, htr789a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hc018yx, hc6810yz, htr012a, htr089a, htr126a, htr2610a, htr3810a, htr389a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc013yx, hc678yz, htr012a, htr035a, htr126a, htr268a, htr357a, htr578a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc015yx, hc568zy, htr012a, htr057a, htr126a, htr268a, htr357a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc015yx, hc368zy, htr012a, htr058a, htr126a, htr268a, htr3810a, htr5810a]
          ·
            linarith only [hlam, hd56b, hd68a, htr356a, htr358a, htr5810a, htr6810a]
      ·
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr039a, htr039b, htr039c, _, _⟩
            linarith only [hlam, hc234yz, htr034a, htr039a, htr249a, htr349b])
          obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, hc345zy, htr245a, htr249a, htr359a, htr459c])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hc459xy, htr245a, htr249b, htr2910a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd39b, hd45a, htr245a, htr249a, htr3910a, htr4910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr035a, htr039a, htr235a, htr3910a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          rcases m.htr 5 9 10 (by decide) (by decide) with
            ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          ·
            linarith only [hlam, hc013yx, hc6910yz, htr012a, htr035a, htr126a, htr2610a, htr359a, htr5910a]
          ·
            linarith only [hlam, hd45a, hd59b, htr245a, htr249a, htr4910a, htr5910a]
        ·
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, htr249b, htr2910a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, hc347zy, htr2410a, htr247a, htr3710a, htr4710c])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
              linarith only [hlam, hc348zy, htr2410a, htr248a, htr3810a, htr4810c])
            obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc478yz, htr2410a, htr248a, htr4810c, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              linarith only [hlam, hc489yz, htr2410a, htr249a, htr4910c, htr8910a])
            obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd23a, hd910b, htr237a, htr378a, htr789a, htr8910a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd34b, hd47a, htr034a, htr037a, htr378a, htr478a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hd23a, hd710b, htr037a, htr038a, htr238a, htr3710a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              rcases m.htr 3 8 9 (by decide) (by decide) with
                ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
              ·
                linarith only [hlam, hc013yx, hc6910yz, htr012a, htr038a, htr126a, htr2610a, htr389a, htr8910a]
              ·
                linarith only [hlam, hd47a, hd810b, htr3810a, htr389a, htr478a, htr789a]
            ·
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc013yx, hc6810yz, htr012a, htr037a, htr126a, htr2610a, htr378a, htr7810a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hd23a, hd810b, htr037a, htr038a, htr237a, htr3810a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              rcases m.htr 3 8 9 (by decide) (by decide) with
                ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd810b, htr238a, htr389a, htr7810a, htr789a]
              ·
                linarith only [hlam, hd34b, hd68a, htr034a, htr038a, htr389a, htr689a]
          ·
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd23a, hd910b, htr237a, htr378a, htr789a, htr8910a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hd34b, hd47a, htr034a, htr037a, htr378a, htr478a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                  linarith only [hlam, hc347zy, htr037a, htr038a, htr378b, htr478a])
                obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
                rcases m.htr 3 8 9 (by decide) (by decide) with
                  ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
                ·
                  linarith only [hlam, hc013yx, hc6910yz, htr012a, htr038a, htr126a, htr2610a, htr389a, htr8910a]
                ·
                  linarith only [hlam, hc347zy, htr378c, htr389a, htr478a, htr789a]
              ·
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc568zy, htr589a, htr689b, htr6910a, htr8910a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 5 7 8 (by decide) (by decide) with
                  ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                ·
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                    linarith only [hlam, hc023zy, htr035a, htr235b, htr257a, htr357a])
                  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
                  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                    linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
                  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                  rcases m.htr 3 7 8 (by decide) (by decide) with
                    ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
                  ·
                    linarith only [hlam, hc013yx, hc689yz, htr012a, htr037a, htr126a, htr269a, htr378a, htr789a]
                  ·
                    linarith only [hlam, hc345zy, htr357c, htr378a, htr457a, htr578a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc045zy, htr057a, htr457b, htr478a, htr578a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc457yz, htr057a, htr058a, htr478a, htr578b])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hc345zy, htr357a, htr457b, htr478a, htr578a])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                    linarith only [hlam, hc457yz, htr357a, htr358a, htr478a, htr578b])
                  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                    linarith only [hlam, hc013yx, hc689yz, htr012a, htr035a, htr126a, htr269a, htr358a, htr589a])
                  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hc015yx, hc689yz, htr012a, htr058a, htr126a, htr269a, htr589b, htr5910a, htr8910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  rcases m.htr 7 9 10 (by decide) (by decide) with
                    ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  ·
                    rcases m.htr 5 7 9 (by decide) (by decide) with
                      ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                    ·
                      linarith only [hlam, hd47a, hd89b, htr478a, htr578a, htr579a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hc457yz, htr479a, htr579c, htr5910a, htr7910a]
                  ·
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                      linarith only [hlam, hd23a, hd79b, htr035a, htr037a, htr235a, htr379a])
                    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hd34b, hd47a, htr034a, htr037a, htr378a, htr478a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 5 7 9 (by decide) (by decide) with
                      ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                    ·
                      linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr578a, htr579a]
                    ·
                      linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
            ·
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc678yz, htr378a, htr379a, htr689a, htr789b])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc678yz, htr578a, htr579a, htr689a, htr789b])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc013yx, hc6910yz, htr012a, htr037a, htr126a, htr2610a, htr379a, htr7910a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              rcases m.htr 3 5 7 (by decide) (by decide) with
                ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd910b, htr235a, htr357a, htr579a, htr7910a]
              ·
                linarith only [hlam, hc023zy, htr035a, htr235b, htr257a, htr357a]

theorem shard_610 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr458a : m.d 4 5 + lam ≤ m.d 5 8)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr459c : m.d 4 9 < m.d 5 9)
    : False :=
  proof_shard_610 m htr012a htr014b htr017a htr045c htr124a htr124b htr126a htr127a htr128a htr129a htr146a htr146b htr146c htr234b htr235a htr235b htr237a htr238a htr245a htr246a htr246b htr257a htr346a htr346b htr356a htr456c htr457a htr457b htr457c htr458a htr458c htr459c

#print axioms shard_610
end Jsp404.NoSatElevenDBMTerminal
