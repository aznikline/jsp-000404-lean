import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_571 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc279xy, hc279yx, hc279yz, hc279zy⟩ := endpoint_caps m 2 7 9 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr124b, htr126c, htr146b])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr125b, htr126c, htr156b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr124c, htr146a, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc456yx, htr124a, htr126a, htr245a, htr246b])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr125c, htr156a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc567xy, htr125a, htr126a, htr256b, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc568xy, htr125a, htr126a, htr256b, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, hc569xy, htr125a, htr126a, htr256b, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, hc5610xy, htr125a, htr126a, htr2510a, htr256b])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd02b, hd67a, htr024a, htr124a, htr126a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd02b, hd68a, htr024a, htr124a, htr126a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd02b, hd69a, htr024a, htr124a, htr126a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd02b, hd610a, htr024a, htr124a, htr126a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc245zy, htr125a, htr126a, htr256b, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr025a, htr257a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr025a, htr258a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr025a, htr259a, htr456a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr025a, htr2510a, htr4510a, htr456a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, htr256b, htr267a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd02b, hd78a, htr024a, htr245a, htr457a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd02b, hd79a, htr024a, htr245a, htr457a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
    linarith only [hlam, hd02b, hd710a, htr024a, htr245a, htr457a, htr5710a])
  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd02b, hd89a, htr024a, htr245a, htr458a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
    linarith only [hlam, hd02b, hd810a, htr024a, htr245a, htr458a, htr5810a])
  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd02b, hd910a, htr024a, htr245a, htr459a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc236yz, htr126a, htr127a, htr267c, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      rcases m.htr 0 3 6 (by decide) (by decide) with
        ⟨htr036a, htr036b, htr036c, _, _⟩ | ⟨htr036a, htr036b, htr036c, _, _⟩
      ·
        linarith only [hlam, hc023yx, hc578yz, htr024a, htr036a, htr245a, htr367a, htr458a, htr678a]
      ·
        linarith only [hlam, hd23a, hd78b, htr036a, htr037a, htr236a, htr367c, htr678a]
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc357zy, htr037a, htr038a, htr238c, htr278b, htr578a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc567yz, htr367a, htr368a, htr578a, htr678b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc567yz, htr368c, htr389a, htr578a, htr678c, htr789a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd23a, hd89b, htr036a, htr038a, htr236a, htr389a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc023yx, hc589yz, htr024a, htr036a, htr245a, htr368a, htr459a, htr689a]
      ·
        linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
  ·
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd02b, hd57a, htr024a, htr124a, htr127c, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd02b, hd57a, htr024a, htr124a, htr127c, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
      linarith only [hlam, hd02b, hd57a, htr024a, htr124a, htr127c, htr1710a, htr5710a])
    obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, htr127b, htr178a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, htr127b, htr179a, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, htr127b, htr1710a, htr2710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc236yz, htr126a, htr128a, htr268c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc237yz, htr127a, htr128a, htr278c, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267yz, htr127a, htr128a, htr278c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        rcases m.htr 3 6 7 (by decide) (by decide) with
          ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a]
        ·
          linarith only [hlam, hd26a, hd89b, htr267a, htr367a, htr368a, htr678c, htr789a]
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc358zy, htr038a, htr039a, htr239c, htr289b, htr589a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc568yz, htr269c, htr289b, htr368a, htr369a, htr589a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
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
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr036a, htr039a, htr236a, htr3910a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc023yx, hc5910yz, htr024a, htr036a, htr245a, htr369a, htr4510a, htr679c, htr7910a]
        ·
          linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a]
    ·
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd02b, hd58a, htr024a, htr124a, htr128c, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hd02b, hd58a, htr024a, htr124a, htr128c, htr1810a, htr5810a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, htr128b, htr189a, htr289a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, htr128b, htr1810a, htr2810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc236yz, htr126a, htr129a, htr269c, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc237yz, htr127a, htr129a, htr279c, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc267yz, htr127a, htr129a, htr279c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278yz, htr128a, htr129a, htr289c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd26a, hd34b, htr034a, htr036a, htr267a, htr367a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23a, hd69b, htr036a, htr037a, htr237a, htr369a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hc023yx, hc589yz, htr024a, htr037a, htr245a, htr378a, htr459a, htr789a]
          ·
            linarith only [hlam, hd26a, hd79b, htr267a, htr378a, htr379a, htr678a]
        ·
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc023yx, hc579yz, htr024a, htr036a, htr245a, htr367a, htr459a, htr679a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23a, hd79b, htr036a, htr037a, htr236a, htr379a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr678a, htr679a]
          ·
            linarith only [hlam, hd34b, hd57a, htr034a, htr037a, htr378a, htr578a]
      ·
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hd02b, hd59a, htr024a, htr124a, htr129c, htr1910a, htr5910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, htr129b, htr1910a, htr2910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, hc027zy, htr0710a, htr1210a, htr127a, htr2710c])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, hc236yz, htr1210a, htr126a, htr2610c, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, hc237yz, htr1210a, htr127a, htr2710c, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc267yz, htr1210a, htr127a, htr2710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc278yz, htr1210a, htr128a, htr2810c, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc279yz, htr1210a, htr129a, htr2910c, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd26a, hd710b, htr0710a, htr078a, htr267a, htr678a])
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
              linarith only [hlam, hd26a, hd34b, htr034a, htr036a, htr267a, htr367a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23a, hd610b, htr036a, htr037a, htr237a, htr3610a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            rcases m.htr 3 7 9 (by decide) (by decide) with
              ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
            ·
              linarith only [hlam, hc023yx, hc5910yz, htr024a, htr037a, htr245a, htr379a, htr4510a, htr7910a]
            ·
              linarith only [hlam, hc027yx, hc5710yz, htr024a, htr079a, htr245a, htr3710a, htr379a, htr4510a]
          ·
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc027yx, hc5710yz, htr024a, htr078a, htr245a, htr4510a, htr6710a, htr678a])
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
              linarith only [hlam, hc023yx, hc5710yz, htr024a, htr036a, htr245a, htr367a, htr4510a, htr6710a])
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
                linarith only [hlam, hd26a, hd34b, htr034a, htr036a, htr267a, htr367a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc236yz, htr036a, htr037a, htr267a, htr367b])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              rcases m.htr 3 7 8 (by decide) (by decide) with
                ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
              ·
                linarith only [hlam, hc023yx, hc589yz, htr024a, htr037a, htr245a, htr378a, htr459a, htr789a]
              ·
                linarith only [hlam, hc236yz, htr267a, htr367c, htr378a, htr678a]
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
                linarith only [hlam, hc023yx, hc5910yz, htr024a, htr037a, htr245a, htr379a, htr4510a, htr7910a])
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
                linarith only [hlam, hc236yz, htr036a, htr039a, htr267a, htr367b, htr379b]
              ·
                linarith only [hlam, hd26a, hd34b, htr034a, htr036a, htr267a, htr367a]
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
              linarith only [hlam, hc023yx, hc589yz, htr024a, htr036a, htr245a, htr368a, htr459a, htr689a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              linarith only [hlam, hc026yx, hc5910yz, htr024a, htr068a, htr245a, htr4510a, htr689a, htr8910a])
            obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc026yx, hc589yz, htr024a, htr069a, htr245a, htr459a, htr6910a, htr8910a])
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

theorem shard_571 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    : False :=
  proof_shard_571 m htr024a htr025a htr034a htr123a htr124a htr124b htr124c htr125a htr125b htr125c htr126a htr126c htr236a htr237a htr237c htr238c htr239c

#print axioms shard_571
end Jsp404.NoSatElevenDBMTerminal
