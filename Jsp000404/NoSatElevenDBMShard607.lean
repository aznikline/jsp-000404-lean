import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_607 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd07a, hd07braw⟩ := m.hrange 0 7 (by decide)
  have hd07b : m.d 0 7 < 4*lam := by
    linarith only [hd07braw, hp]
  obtain ⟨hd08a, hd08braw⟩ := m.hrange 0 8 (by decide)
  have hd08b : m.d 0 8 < 4*lam := by
    linarith only [hd08braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < 4*lam := by
    linarith only [hd38braw, hp]
  obtain ⟨hd39a, hd39braw⟩ := m.hrange 3 9 (by decide)
  have hd39b : m.d 3 9 < 4*lam := by
    linarith only [hd39braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
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
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc047xy, hc047yx, hc047yz, hc047zy⟩ := endpoint_caps m 0 4 7 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5810xy, hc5810yx, hc5810yz, hc5810zy⟩ := endpoint_caps m 5 8 10 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr045a, htr046a, htr456c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc234yz, htr125b, htr156a, htr245b, htr345a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr034c, htr045a, htr346a, htr456c])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd01b, hd69a, htr012a, htr125a, htr256a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr269a, htr569a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hd01b, hd610a, htr012a, htr125a, htr256a, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr2610a, htr5610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc234yz, htr034a, htr036a, htr246a, htr346b])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc234yz, htr145a, htr146a, htr246a, htr345a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc234yz, htr145c, htr156c, htr167a, htr246b, htr267a, htr345a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr146b, htr147c, htr167b])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc234yz, htr246b, htr267a, htr345a, htr456c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc024zy, htr046c, htr067a, htr246a, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr036b, htr037c, htr067b])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc234yz, htr246a, htr346c, htr367a, htr467a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hd23a, hd67b, htr036a, htr038a, htr238a, htr367a])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc234yz, htr246b, htr268a, htr345a, htr456c, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc234yz, htr246a, htr346c, htr368a, htr468a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      rcases m.htr 4 5 7 (by decide) (by decide) with
        ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
      ·
        linarith only [hlam, hc567xy, htr034c, htr045a, htr347a, htr456a, htr457c]
      ·
        linarith only [hlam, hc457zy, htr034c, htr045a, htr347a, htr457a]
    ·
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          linarith only [hlam, hc568xy, htr034c, htr045a, htr348a, htr456a, htr458c]
        ·
          linarith only [hlam, hc458zy, htr034c, htr045a, htr348a, htr458a]
      ·
        rcases m.htr 2 5 7 (by decide) (by decide) with
          ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
        ·
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc234yz, htr035c, htr057a, htr245a, htr345c, htr457a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc234yz, htr245a, htr345c, htr357a, htr457a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc567xy, htr057a, htr058a, htr456a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, htr245c, htr258a, htr458a])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, hc567xy, htr357a, htr358a, htr456a, htr458a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              rcases m.htr 4 5 10 (by decide) (by decide) with
                ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              ·
                rcases m.htr 2 7 8 (by decide) (by decide) with
                  ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
                ·
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc013yx, hc789yx, htr012a, htr035a, htr127a, htr279a, htr357a, htr578a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc567xy, htr256a, htr257b, htr279a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc013yx, hc789zy, htr012a, htr035a, htr128a, htr289a, htr357a, htr579a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc568xy, htr256a, htr258b, htr289a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd56a, hd89b, htr256a, htr257a, htr578a, htr789a]
                  ·
                    linarith only [hlam, hd24a, hd78b, htr245a, htr458a, htr589a, htr789a]
                ·
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc013yx, hc789xy, htr012a, htr035a, htr127a, htr278a, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc567xy, htr256a, htr257b, htr279a, htr579a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc013yx, hc789yz, htr012a, htr035a, htr127a, htr279a, htr358a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc568xy, htr256a, htr258b, htr289a, htr589a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
                  ·
                    linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
              ·
                have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                  linarith only [hlam, htr045b, htr0510a, htr4510a])
                obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0510c, htr057b, htr0710b])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0510c, htr058b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                  linarith only [hlam, hc567xy, htr057c, htr0710a, htr256a, htr257b, htr2710a])
                obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc568xy, htr058c, htr0810a, htr256a, htr258b, htr2810a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc013yx, hc7810yx, htr012a, htr035a, htr127a, htr2710a, htr357a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr2810a, htr7810a]
                ·
                  linarith only [hlam, hd01b, hd810a, htr012a, htr127a, htr278a, htr7810a]
            ·
              have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                linarith only [hlam, htr045b, htr059a, htr459a])
              obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr057b, htr059c, htr079b])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr058b, htr059c, htr089b])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc567xy, htr057c, htr079a, htr256a, htr257b, htr279a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc568xy, htr058c, htr089a, htr256a, htr258b, htr289a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc013yx, hc789yx, htr012a, htr035a, htr127a, htr279a, htr357a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
              ·
                linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
          ·
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr045b, htr058a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr057b, htr058c, htr078b])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, hc567xy, htr256a, htr258a, htr457a, htr458a])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc567xy, htr057c, htr078a, htr256a, htr257b, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, htr345b, htr358a, htr458a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc013yx, hc789xy, htr012a, htr035a, htr127a, htr278a, htr357a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc567xy, htr256a, htr257b, htr279a, htr579a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc578yx, htr357a, htr358c, htr389a, htr589a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            rcases m.htr 6 8 9 (by decide) (by decide) with
              ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
            ·
              linarith only [hlam, hc013yx, hc789yz, htr012a, htr036a, htr127a, htr279a, htr368a, htr689a]
            ·
              linarith only [hlam, hc013yx, hc568yz, htr012a, htr038a, htr125a, htr258a, htr389a, htr689a]
        ·
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr278a, htr578a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc234yz, htr246b, htr267b, htr278a, htr347a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr279a, htr579a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc234yz, htr246b, htr267b, htr279a, htr347a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc134yz, htr147a, htr347c, htr379a, htr479a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc013yx, hc567yz, htr012a, htr037a, htr125a, htr257a, htr378a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hc013yx, hc578yz, htr012a, htr036a, htr125a, htr258a, htr367a, htr678a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc013yx, hc567yz, htr012a, htr037a, htr125a, htr257a, htr379a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc013yx, hc789zy, htr012a, htr036a, htr128a, htr289a, htr367a, htr679a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc568xy, htr256a, htr258b, htr289a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a]
          ·
            linarith only [hlam, hd56a, hd78b, htr256a, htr258a, htr589a, htr789a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc467xy, htr045a, htr047a, htr124b, htr145a, htr246a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc468xy, htr045a, htr048a, htr124b, htr145a, htr246a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr049a, htr049b, htr049c, _, _⟩
      linarith only [hlam, hc469xy, htr045a, htr049a, htr124b, htr145a, htr246a])
    obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, htr034c, htr047a, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, htr034c, htr048a, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr349a, htr349b, htr349c, _, _⟩
      linarith only [hlam, htr034c, htr049a, htr349a])
    obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr124b, htr145a, htr246a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr124b, htr145a, htr246a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr258a, htr345a, htr458a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569xy, htr124b, htr145a, htr246a, htr456b, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr259a, htr345a, htr459a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
      linarith only [hlam, hc5610xy, htr124b, htr145a, htr246a, htr4510a, htr456b])
    obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
    have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr2510a, htr345a, htr4510a])
    obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr246b, htr267a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr246b, htr268a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, htr246b, htr269a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, htr246b, htr2610a, htr4610a])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr278a, htr578a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd01b, hd710a, htr012a, htr125a, htr257a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr2710a, htr5710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd01b, hd58a, htr012a, htr128a, htr289a, htr589a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
      linarith only [hlam, hd01b, hd810a, htr012a, htr125a, htr258a, htr5810a])
    obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
      linarith only [hlam, hd01b, hd58a, htr012a, htr128a, htr2810a, htr5810a])
    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd01b, hd910a, htr012a, htr125a, htr259a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
      linarith only [hlam, hd01b, hd59a, htr012a, htr129a, htr2910a, htr5910a])
    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
    rcases m.htr 2 4 7 (by decide) (by decide) with
      ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc234yz, htr034a, htr037a, htr247a, htr347b])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc346zy, htr246a, htr247a, htr367a, htr467c])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467xy, htr246a, htr247b, htr278a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd07b, hd46a, htr078a, htr246a, htr247a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
        linarith only [hlam, hd46a, hd78b, htr0710a, htr078a, htr246a, htr247b, htr2710a])
      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd37b, hd46a, htr246a, htr247a, htr378a, htr478a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr036a, htr037a, htr236a, htr378a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      rcases m.htr 6 7 10 (by decide) (by decide) with
        ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      ·
        linarith only [hlam, hc013yx, hc5710yz, htr012a, htr036a, htr125a, htr2510a, htr367a, htr6710a]
      ·
        linarith only [hlam, hd46a, hd67b, htr047b, htr0710a, htr246a, htr247a, htr6710a]
    ·
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, htr247b, htr2710a, htr4710a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      rcases m.htr 2 4 8 (by decide) (by decide) with
        ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
      ·
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc234yz, htr034a, htr038a, htr248a, htr348b])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc346zy, htr246a, htr248a, htr368a, htr468c])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc468xy, htr246a, htr248b, htr289a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hd08b, hd46a, htr089a, htr246a, htr248a, htr489a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, hd46a, hd89b, htr0810a, htr089a, htr246a, htr248b, htr2810a])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd38b, hd46a, htr246a, htr248a, htr389a, htr489a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr036a, htr038a, htr236a, htr389a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        rcases m.htr 6 8 10 (by decide) (by decide) with
          ⟨htr6810a, htr6810b, htr6810c, _, _⟩ | ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        ·
          linarith only [hlam, hc013yx, hc5810yz, htr012a, htr036a, htr125a, htr2510a, htr368a, htr6810a]
        ·
          linarith only [hlam, hd46a, hd68b, htr048b, htr0810a, htr246a, htr248a, htr6810a]
      ·
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, htr248b, htr2810a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr039a, htr039b, htr039c, _, _⟩
            linarith only [hlam, hc234yz, htr034a, htr039a, htr249a, htr349b])
          obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, hc346zy, htr246a, htr249a, htr369a, htr469c])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hc469xy, htr246a, htr249b, htr2910a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd39b, hd46a, htr246a, htr249a, htr3910a, htr4910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr036a, htr039a, htr236a, htr3910a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          rcases m.htr 6 9 10 (by decide) (by decide) with
            ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          ·
            linarith only [hlam, hc013yx, hc5910yz, htr012a, htr036a, htr125a, htr2510a, htr369a, htr6910a]
          ·
            linarith only [hlam, hd46a, hd69b, htr246a, htr249a, htr4910a, htr6910a]
        ·
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, htr249b, htr2910a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, hc047zy, htr0710a, htr2410a, htr247a, htr4710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, hc346zy, htr2410a, htr246a, htr3610a, htr4610c])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, hc347zy, htr2410a, htr247a, htr3710a, htr4710c])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc467yz, htr2410a, htr247a, htr4710c, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc478yz, htr2410a, htr248a, htr4810c, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc479yz, htr2410a, htr249a, htr4910c, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hd56a, hd710b, htr0710a, htr078a, htr567a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hd57a, hd810b, htr078a, htr079a, htr579a, htr7810a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd23a, hd810b, htr236a, htr367a, htr678a, htr7810a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr034a, htr036a, htr367a, htr567a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd23a, hd610b, htr036a, htr037a, htr237a, htr3610a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              rcases m.htr 3 7 9 (by decide) (by decide) with
                ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
              ·
                linarith only [hlam, hc013yx, hc5910yz, htr012a, htr037a, htr125a, htr2510a, htr379a, htr7910a]
              ·
                linarith only [hlam, hc017yx, hc5710yz, htr012a, htr079a, htr125a, htr2510a, htr3710a, htr379a]
            ·
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc017yx, hc5710yz, htr012a, htr078a, htr125a, htr2510a, htr6710a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hd57a, hd910b, htr078a, htr079a, htr578a, htr7910a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc013yx, hc5710yz, htr012a, htr036a, htr125a, htr2510a, htr367a, htr6710a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd23a, hd710b, htr036a, htr037a, htr236a, htr3710a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              rcases m.htr 3 7 9 (by decide) (by decide) with
                ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd710b, htr0710a, htr079a, htr237a, htr379a]
              ·
                linarith only [hlam, hd34b, hd57a, htr034a, htr037a, htr379a, htr579a]
          ·
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                  linarith only [hlam, hd34b, hd56a, htr034a, htr036a, htr367a, htr567a])
                obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hc356zy, htr036a, htr037a, htr367b, htr567a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                rcases m.htr 3 7 8 (by decide) (by decide) with
                  ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
                ·
                  linarith only [hlam, hc013yx, hc589yz, htr012a, htr037a, htr125a, htr259a, htr378a, htr789a]
                ·
                  linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a]
              ·
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc357zy, htr378a, htr578b, htr589a, htr789a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc578yz, htr378a, htr379a, htr589a, htr789b])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc578yz, htr589a, htr678a, htr679a, htr789b])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                  linarith only [hlam, hc578yz, htr379c, htr3910a, htr589a, htr789c, htr8910a])
                obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hc013yx, hc5910yz, htr012a, htr037a, htr125a, htr2510a, htr379a, htr7910a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr039a, htr039b, htr039c, _, _⟩
                  linarith only [hlam, hd23a, hd910b, htr037a, htr039a, htr237a, htr3910a])
                obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hd23a, hd910b, htr236a, htr367a, htr679a, htr7910a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                rcases m.htr 0 3 6 (by decide) (by decide) with
                  ⟨htr036a, htr036b, htr036c, _, _⟩ | ⟨htr036a, htr036b, htr036c, _, _⟩
                ·
                  linarith only [hlam, hc356zy, htr036a, htr039a, htr367b, htr379b, htr567a]
                ·
                  linarith only [hlam, hd34b, hd56a, htr034a, htr036a, htr367a, htr567a]
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc567yz, htr367a, htr368a, htr578a, htr678b])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, hc567yz, htr068c, htr089a, htr578a, htr678c, htr789a])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr068b, htr069c, htr089b])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc013yx, hc589yz, htr012a, htr036a, htr125a, htr259a, htr368a, htr689a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc016yx, hc5910yz, htr012a, htr068a, htr125a, htr2510a, htr689a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc016yx, hc589yz, htr012a, htr069a, htr125a, htr259a, htr6910a, htr8910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hd23a, hd79b, htr036a, htr037a, htr236a, htr367c, htr679a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                rcases m.htr 3 7 8 (by decide) (by decide) with
                  ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
                ·
                  linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr678a, htr679a]
                ·
                  linarith only [hlam, hd34b, hd57a, htr034a, htr037a, htr378a, htr578a]
              ·
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
                ·
                  linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]

theorem shard_607 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_607 m htr012a htr034a htr034c htr035a htr035c htr045a htr045b htr124b htr125a htr125b htr126a htr127a htr128a htr129a htr145a htr145c htr236a htr237a htr238a htr245a htr245b htr245c htr345a htr345b htr345c htr456a htr456b htr456c

#print axioms shard_607
end Jsp404.NoSatElevenDBMTerminal
