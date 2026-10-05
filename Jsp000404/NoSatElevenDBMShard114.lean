import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_114 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr249c : m.d 2 9 < m.d 4 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
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
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc279xy, hc279yx, hc279yz, hc279zy⟩ := endpoint_caps m 2 7 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr025b, htr026c, htr056b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr025c, htr056a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc567xy, htr025a, htr026a, htr256b, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc568xy, htr025a, htr026a, htr256b, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, hc569xy, htr025a, htr026a, htr256b, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd12b, hd67a, htr023a, htr026a, htr123a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd12b, hd68a, htr023a, htr026a, htr123a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd12b, hd69a, htr023a, htr026a, htr123a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd12b, hd610a, htr023a, htr026a, htr123a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd12b, hd35a, htr023a, htr026a, htr123a, htr256b, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr125a, htr257a, htr356a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr125a, htr258a, htr356a, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr125a, htr259a, htr356a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, htr256b, htr267a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd12b, hd78a, htr123a, htr235a, htr357a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd12b, hd79a, htr123a, htr235a, htr357a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
    linarith only [hlam, hd12b, hd710a, htr123a, htr235a, htr357a, htr5710a])
  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd12b, hd89a, htr123a, htr235a, htr358a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
    linarith only [hlam, hd12b, hd810a, htr123a, htr235a, htr358a, htr5810a])
  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd12b, hd910a, htr123a, htr235a, htr359a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 0 2 7 (by decide) (by decide) with
    ⟨htr027a, htr027b, htr027c, _, _⟩ | ⟨htr027a, htr027b, htr027c, _, _⟩
  ·
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc124zy, htr024a, htr027a, htr147a, htr247c])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246yz, htr026a, htr027a, htr267c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a]
      ·
        linarith only [hlam, hd24a, hd78b, htr146a, htr147a, htr246a, htr467c, htr678a]
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd24a, hd67b, htr024a, htr027a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc457zy, htr147a, htr148a, htr248c, htr278b, htr578a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc567yz, htr467a, htr468a, htr578a, htr678b])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc567yz, htr468c, htr489a, htr578a, htr678c, htr789a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd24a, hd89b, htr146a, htr148a, htr246a, htr489a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd89b, htr014a, htr146a, htr468a, htr689a]
      ·
        linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
  ·
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hd12b, hd57a, htr023a, htr027c, htr078a, htr123a, htr578a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
      linarith only [hlam, hd12b, hd57a, htr023a, htr027c, htr079a, htr123a, htr579a])
    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
      linarith only [hlam, hd12b, hd57a, htr023a, htr027c, htr0710a, htr123a, htr5710a])
    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, htr027b, htr078a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, htr027b, htr079a, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, htr027b, htr0710a, htr2710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    rcases m.htr 0 2 8 (by decide) (by decide) with
      ⟨htr028a, htr028b, htr028c, _, _⟩ | ⟨htr028a, htr028b, htr028c, _, _⟩
    ·
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc124zy, htr024a, htr028a, htr148a, htr248c])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc246yz, htr026a, htr028a, htr268c, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc247yz, htr027a, htr028a, htr278c, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267yz, htr027a, htr028a, htr278c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a]
        ·
          linarith only [hlam, hd26a, hd89b, htr267a, htr467a, htr468a, htr678c, htr789a]
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd24a, hd78b, htr024a, htr028a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr149a, htr149b, htr149c, _, _⟩
          linarith only [hlam, hc458zy, htr148a, htr149a, htr249c, htr289b, htr589a])
        obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc568yz, htr269c, htr289b, htr468a, htr469a, htr589a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc578yz, htr478a, htr479a, htr589a, htr789b])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc578yz, htr589a, htr678a, htr679a, htr789b])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc578yz, htr479c, htr4910a, htr589a, htr789c, htr8910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hd24a, hd910b, htr146a, htr149a, htr246a, htr4910a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd910b, htr014a, htr146a, htr469a, htr679c, htr7910a]
        ·
          linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a]
    ·
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, hd12b, hd58a, htr023a, htr028c, htr089a, htr123a, htr589a])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
        linarith only [hlam, hd12b, hd58a, htr023a, htr028c, htr0810a, htr123a, htr5810a])
      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, htr028b, htr089a, htr289a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, htr028b, htr0810a, htr2810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      rcases m.htr 0 2 9 (by decide) (by decide) with
        ⟨htr029a, htr029b, htr029c, _, _⟩ | ⟨htr029a, htr029b, htr029c, _, _⟩
      ·
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc246yz, htr026a, htr029a, htr269c, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc247yz, htr027a, htr029a, htr279c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc267yz, htr027a, htr029a, htr279c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278yz, htr028a, htr029a, htr289c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hc124zy, htr146a, htr246b, htr267a, htr467a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd24a, hd69b, htr146a, htr147a, htr247a, htr469a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
          ·
            linarith only [hlam, hd26a, hd79b, htr267a, htr478a, htr479a, htr678a]
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd01a, hd79b, htr014a, htr146a, htr467a, htr679a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd24a, hd79b, htr146a, htr147a, htr246a, htr479a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd24a, hd79b, htr247a, htr478a, htr678a, htr679a]
          ·
            linarith only [hlam, hd45b, hd57a, htr145a, htr147a, htr478a, htr578a]
      ·
        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
          linarith only [hlam, hd12b, hd59a, htr023a, htr029c, htr0910a, htr123a, htr5910a])
        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, htr029b, htr0910a, htr2910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 0 2 10 (by decide) (by decide) with
          ⟨htr0210a, htr0210b, htr0210c, _, _⟩ | ⟨htr0210a, htr0210b, htr0210c, _, _⟩
        ·
          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
            linarith only [hlam, hc127zy, htr0210a, htr027a, htr1710a, htr2710c])
          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc246yz, htr0210a, htr026a, htr2610c, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, hc247yz, htr0210a, htr027a, htr2710c, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc267yz, htr0210a, htr027a, htr2710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc278yz, htr0210a, htr028a, htr2810c, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc279yz, htr0210a, htr029a, htr2910c, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hd26a, hd710b, htr1710a, htr178a, htr267a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hd57a, hd810b, htr178a, htr179a, htr579a, htr7810a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd24a, hd810b, htr246a, htr467a, htr678a, htr7810a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hc124zy, htr146a, htr246b, htr267a, htr467a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd24a, hd610b, htr146a, htr147a, htr247a, htr4610a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd01a, hd910b, htr014a, htr147a, htr479a, htr7910a]
            ·
              linarith only [hlam, hd01a, hd710b, htr017a, htr179a, htr4710a, htr479a]
          ·
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hd01a, hd710b, htr017a, htr178a, htr6710a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hd57a, hd910b, htr178a, htr179a, htr578a, htr7910a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd01a, hd710b, htr014a, htr146a, htr467a, htr6710a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd24a, hd710b, htr146a, htr147a, htr246a, htr4710a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd24a, hd710b, htr1710a, htr179a, htr247a, htr479a]
            ·
              linarith only [hlam, hd45b, hd57a, htr145a, htr147a, htr479a, htr579a]
        ·
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hc124zy, htr146a, htr246b, htr267a, htr467a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hc246yz, htr146a, htr147a, htr267a, htr467b])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
              ·
                linarith only [hlam, hc246yz, htr267a, htr467c, htr478a, htr678a]
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc578yz, htr478a, htr479a, htr589a, htr789b])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc578yz, htr589a, htr678a, htr679a, htr789b])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc578yz, htr479c, htr4910a, htr589a, htr789c, htr8910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd01a, hd910b, htr014a, htr147a, htr479a, htr7910a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr149a, htr149b, htr149c, _, _⟩
                linarith only [hlam, hd24a, hd910b, htr147a, htr149a, htr247a, htr4910a])
              obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd24a, hd910b, htr246a, htr467a, htr679a, htr7910a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              rcases m.htr 1 4 6 (by decide) (by decide) with
                ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
              ·
                linarith only [hlam, hc246yz, htr146a, htr149a, htr267a, htr467b, htr479b]
              ·
                linarith only [hlam, hc124zy, htr146a, htr246b, htr267a, htr467a]
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc567yz, htr467a, htr468a, htr578a, htr678b])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc567yz, htr168c, htr189a, htr578a, htr678c, htr789a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, htr168b, htr169c, htr189b])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd01a, hd89b, htr014a, htr146a, htr468a, htr689a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              linarith only [hlam, hd01a, hd910b, htr016a, htr168a, htr689a, htr8910a])
            obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hd01a, hd89b, htr016a, htr169a, htr6910a, htr8910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd24a, hd79b, htr146a, htr147a, htr246a, htr467c, htr679a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hd24a, hd79b, htr247a, htr478a, htr678a, htr679a]
              ·
                linarith only [hlam, hd45b, hd57a, htr145a, htr147a, htr478a, htr578a]
            ·
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
              ·
                linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]

theorem shard_114 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr249c : m.d 2 9 < m.d 4 9)
    : False :=
  proof_shard_114 m htr014a htr016a htr017a htr023a htr024a htr025a htr025b htr025c htr026a htr026c htr123a htr125a htr145a htr235a htr246a htr246b htr247a htr247c htr248c htr249c

#print axioms shard_114
end Jsp404.NoSatElevenDBMTerminal
