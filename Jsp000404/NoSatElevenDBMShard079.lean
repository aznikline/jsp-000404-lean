import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_079 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
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
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc018xy, hc018yx, hc018yz, hc018zy⟩ := endpoint_caps m 0 1 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hc234xy, htr023a, htr026a, htr124a, htr126a])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr024b, htr026c, htr046b])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr025b, htr026c, htr056b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr014c, htr046a, htr124c, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc456yx, htr012c, htr026a, htr124a, htr245a, htr246b])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc234xy, htr023a, htr024b, htr045a, htr245a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc467xy, htr012c, htr026a, htr124a, htr246b, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc234xy, htr023a, htr024b, htr047a, htr247a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc468xy, htr012c, htr026a, htr124a, htr246b, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hc234xy, htr023a, htr024b, htr048a, htr248a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr015c, htr056a, htr125c, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc567xy, htr012c, htr026a, htr125a, htr256b, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc235xy, htr023a, htr025b, htr057a, htr257a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc568xy, htr012c, htr026a, htr125a, htr256b, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hc235xy, htr023a, htr025b, htr058a, htr258a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc245zy, htr125a, htr126a, htr256b, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, htr012c, htr027a, htr127a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr026c, htr027b, htr067c])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr026b, htr067a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc678yx, htr012c, htr026a, htr127a, htr267c, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc246yx, htr124a, htr126c, htr168a, htr268a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hc679yx, htr012c, htr026a, htr127a, htr267c, htr269a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hc246yx, htr124a, htr126c, htr169a, htr269a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, hc6710yx, htr012c, htr026a, htr127a, htr2610a, htr267c])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
      linarith only [hlam, hc246yx, htr124a, htr126c, htr1610a, htr2610a])
    obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc236yz, htr126a, htr127a, htr267c, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr367a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr016a, htr169a, htr367a, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr016a, htr1610a, htr3610a, htr367a])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc237xy, htr023a, htr027b, htr078a, htr278a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
      linarith only [hlam, hd01a, hd810b, htr013a, htr136a, htr368a, htr6810a])
    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hc014xy, hc678zy, htr013a, htr045a, htr136a, htr368a, htr457a, htr578a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc015xy, hc568yz, htr013a, htr057a, htr136a, htr368a, htr457a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      rcases m.htr 5 8 9 (by decide) (by decide) with
        ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
      ·
        linarith only [hlam, hd56a, hd68b, htr456a, htr458a, htr589a, htr689a]
      ·
        linarith only [hlam, hc015xy, hc678zy, htr013a, htr058a, htr136a, htr368a, htr589a, htr789a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc014xy, hc689zy, htr013a, htr047a, htr136a, htr369a, htr478a, htr789a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
        linarith only [hlam, hc467yz, htr078b, htr0810a, htr478a, htr678c, htr6810a])
      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc017xy, hc468yz, htr013a, htr078a, htr136a, htr368a, htr489a, htr789a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hc018xy, hc689zy, htr013a, htr0810a, htr136a, htr369a, htr4810a, htr489a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc015xy, hc689zy, htr013a, htr057a, htr136a, htr369a, htr578a, htr789a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hd56a, hd67b, htr456a, htr457a, htr578a, htr678a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc015xy, hc567yz, htr013a, htr058a, htr136a, htr367a, htr457a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      rcases m.htr 5 8 10 (by decide) (by decide) with
        ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
      ·
        linarith only [hlam, hc014xy, hc568yz, htr013a, htr048a, htr136a, htr368a, htr4810a, htr5810a]
      ·
        linarith only [hlam, hc014xy, hc6810zy, htr013a, htr045a, htr136a, htr3610a, htr458a, htr5810a]
  ·
    have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr027a, htr027b, htr027c, _, _⟩
      linarith only [hlam, hc234xy, htr023a, htr027a, htr124a, htr127a])
    obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc245zy, htr125a, htr127a, htr257b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr028a, htr028b, htr028c, _, _⟩
        linarith only [hlam, htr012c, htr028a, htr128a])
      obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr026c, htr028b, htr068c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr027c, htr028b, htr078c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr026b, htr068a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc678xy, htr012c, htr026a, htr128a, htr267a, htr268c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc246yx, htr124a, htr126c, htr167a, htr267a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr027b, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc236yz, htr126a, htr128a, htr268c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr367a, htr368a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a]
      ·
        linarith only [hlam, hc267yz, htr127a, htr128a, htr278c, htr678a]
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc245zy, htr125a, htr128a, htr258b, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        have hforced029 := (m.htr 0 2 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr029a, htr029b, htr029c, _, _⟩
          linarith only [hlam, htr012c, htr029a, htr129a])
        obtain ⟨htr029a, htr029b, htr029c, _, _⟩ := hforced029
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, htr026c, htr029b, htr069c])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr027c, htr029b, htr079c])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, htr026b, htr069a, htr269a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc679xy, htr012c, htr026a, htr129a, htr267a, htr269c])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc246yx, htr124a, htr126c, htr167a, htr267a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, htr027b, htr079a, htr279a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc236yz, htr126a, htr129a, htr269c, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd01a, hd69b, htr016a, htr167a, htr367a, htr369a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd79b, htr013a, htr136a, htr367a, htr679a]
        ·
          linarith only [hlam, hc267yz, htr127a, htr129a, htr279c, htr679a]
      ·
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
            linarith only [hlam, htr012c, htr0210a, htr1210a])
          obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, htr0210b, htr026c, htr0610c])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0210b, htr027c, htr0710c])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
            linarith only [hlam, htr026b, htr0610a, htr2610a])
          obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc6710xy, htr012c, htr026a, htr1210a, htr2610c, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc246yx, htr124a, htr126c, htr167a, htr267a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
            linarith only [hlam, htr027b, htr0710a, htr2710a])
          obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, hc236yz, htr1210a, htr126a, htr2610c, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd01a, hd610b, htr016a, htr167a, htr3610a, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd710b, htr013a, htr136a, htr367a, htr6710a]
          ·
            linarith only [hlam, hc267yz, htr1210a, htr127a, htr2710c, htr6710a]
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hd24b, hd56a, htr124a, htr126a, htr267a, htr567a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc246yx, htr016c, htr067a, htr124a, htr126c, htr267a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc246yx, htr124a, htr126c, htr167a, htr267a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 3 6 7 (by decide) (by decide) with
              ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
            ·
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc014xy, hc678yx, htr013a, htr045a, htr136a, htr367a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hd24b, hd56a, htr124a, htr126a, htr268a, htr568a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc246yx, htr124a, htr126c, htr168a, htr268a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr367a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc014xy, hc679yx, htr013a, htr045a, htr136a, htr367a, htr456a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hd24b, hd56a, htr124a, htr126a, htr269a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc246yx, htr124a, htr126c, htr169a, htr269a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hd01a, hd67b, htr016a, htr169a, htr367a, htr369a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc014xy, hc678zy, htr013a, htr045a, htr136a, htr368a, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd24b, hd57a, htr124a, htr127a, htr278a, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc247yx, htr124a, htr127c, htr178a, htr278a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc014xy, hc689zy, htr013a, htr045a, htr136a, htr369a, htr458a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd68b, htr017a, htr178a, htr689a, htr789a]
              ·
                linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
            ·
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr367a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              rcases m.htr 5 6 8 (by decide) (by decide) with
                ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc356zy, htr016c, htr068a, htr167a, htr367a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc356zy, htr167a, htr168a, htr367a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                rcases m.htr 5 6 9 (by decide) (by decide) with
                  ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                ·
                  rcases m.htr 5 6 10 (by decide) (by decide) with
                    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                  ·
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hd01a, hd37b, htr016a, htr167a, htr378a, htr678a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc014xy, hc789yx, htr016a, htr045a, htr167a, htr457a, htr579a, htr678a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hc356zy, htr167c, htr179a, htr367a, htr567b, htr579a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr378a, htr379a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc014xy, hc789zy, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc356zy, htr368a, htr568b, htr589a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
                      ·
                        linarith only [hlam, hd01a, hd78b, htr016a, htr168a, htr689a, htr789a]
                    ·
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, hc356zy, htr257b, htr278a, htr367a, htr567b, htr678a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hc014xy, hc789xy, htr016a, htr045a, htr167a, htr457a, htr578a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc356zy, htr257b, htr279a, htr367a, htr567b, htr679a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hd24b, hd78a, htr124a, htr127a, htr279a, htr578a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc014xy, hc789yz, htr013a, htr045a, htr138a, htr389a, htr457a, htr579a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hc014xy, hc378zy, htr018a, htr045a, htr189a, htr389a, htr457a, htr578a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hc248yx, htr124a, htr128c, htr189a, htr289a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd24b, hd78a, htr124a, htr128a, htr289a, htr789a]
                      ·
                        linarith only [hlam, hd24b, hd89a, htr124a, htr127a, htr278a, htr789a]
                  ·
                    have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                      linarith only [hlam, htr056b, htr0610a, htr5610a])
                    obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0610c, htr067b, htr0710b])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, htr0610c, htr068b, htr0810b])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                      linarith only [hlam, hc247yx, htr017c, htr0710a, htr124a, htr127c, htr2710a])
                    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hc248yx, htr018c, htr0810a, htr124a, htr128c, htr2810a])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      linarith only [hlam, hd24b, hd610a, htr124a, htr127a, htr2710a, htr5610a, htr567b, htr5710a])
                    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc014xy, hc7810yx, htr016a, htr045a, htr167a, htr457a, htr5710a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc356zy, htr257b, htr278a, htr367a, htr567b, htr678a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd24b, hd78a, htr124a, htr128a, htr2810a, htr7810a]
                    ·
                      linarith only [hlam, hd24b, hd810a, htr124a, htr127a, htr278a, htr7810a]
                ·
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, htr056b, htr069a, htr569a])
                  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, htr067b, htr069c, htr079b])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, htr068b, htr069c, htr089b])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc247yx, htr017c, htr079a, htr124a, htr127c, htr279a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc248yx, htr018c, htr089a, htr124a, htr128c, htr289a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd24b, hd69a, htr124a, htr127a, htr279a, htr567b, htr569a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc014xy, hc789yx, htr016a, htr045a, htr167a, htr457a, htr579a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc356zy, htr257b, htr278a, htr367a, htr567b, htr678a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd24b, hd78a, htr124a, htr128a, htr289a, htr789a]
                  ·
                    linarith only [hlam, hd24b, hd89a, htr124a, htr127a, htr278a, htr789a]
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, htr056b, htr068a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr067b, htr068c, htr078b])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, htr016c, htr056b, htr168a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc247yx, htr017c, htr078a, htr124a, htr127c, htr278a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd24b, hd68a, htr124a, htr127a, htr278a, htr567b, htr568a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc014xy, hc789xy, htr016a, htr045a, htr167a, htr457a, htr578a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc356zy, htr257b, htr279a, htr367a, htr567b, htr679a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd24b, hd68a, htr124a, htr127a, htr279a, htr567b, htr568a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc014xy, hc789yz, htr013a, htr045a, htr138a, htr389a, htr457a, htr579a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc014xy, hc368zy, htr018a, htr045a, htr189a, htr389a, htr456a, htr568a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd36b, hd78a, htr167a, htr168c, htr189a, htr367a, htr789a]
                ·
                  linarith only [hlam, hd24b, hd89a, htr124a, htr127a, htr278a, htr789a]
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr016c, htr056b, htr167a, htr567a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd24b, hd78a, htr124a, htr126a, htr256b, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd24b, hd67a, htr124a, htr127a, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc247yx, htr124a, htr127c, htr178a, htr278a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc014xy, hc367zy, htr017a, htr045a, htr178a, htr378a, htr456a, htr567a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hc014xy, hc678yz, htr013a, htr045a, htr137a, htr378a, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hd24b, hd67a, htr124a, htr126c, htr168a, htr567a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc014xy, hc789yx, htr013a, htr045a, htr137a, htr378a, htr457a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc678xy, htr167c, htr168a, htr179a, htr567b, htr579a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc014xy, hc367zy, htr017a, htr045a, htr179a, htr379a, htr456a, htr567a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc014xy, hc789zy, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc678xy, htr567a, htr568b, htr589a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a]
            ·
              linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a]

theorem shard_079 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    : False :=
  proof_shard_079 m htr012a htr012c htr013a htr014c htr015c htr016a htr016c htr017a htr017c htr018a htr018c htr023a htr024b htr025b htr124a htr124c htr125a htr125c htr126a htr126c htr136a htr137a htr138a

#print axioms shard_079
end Jsp404.NoSatElevenDBMTerminal
