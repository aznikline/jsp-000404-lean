import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_225 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
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
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
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
  rcases m.htr 1 4 7 (by decide) (by decide) with
    ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
  ·
    rcases m.htr 1 4 8 (by decide) (by decide) with
      ⟨htr148a, htr148b, htr148c, _, _⟩ | ⟨htr148a, htr148b, htr148c, _, _⟩
    ·
      rcases m.htr 1 4 9 (by decide) (by decide) with
        ⟨htr149a, htr149b, htr149c, _, _⟩ | ⟨htr149a, htr149b, htr149c, _, _⟩
      ·
        rcases m.htr 1 4 10 (by decide) (by decide) with
          ⟨htr1410a, htr1410b, htr1410c, _, _⟩ | ⟨htr1410a, htr1410b, htr1410c, _, _⟩
        ·
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hc012xy, hc567yx, htr014a, htr023a, htr145a, htr235a, htr357a, htr456a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd01a, hd67b, htr014a, htr145a, htr456a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd01a, hd68b, htr014a, htr145a, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            rcases m.htr 4 5 7 (by decide) (by decide) with
              ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc012xy, hc567zy, htr014a, htr023a, htr145a, htr236a, htr367a, htr457a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd01a, hd78b, htr014a, htr145a, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd01a, hd79b, htr014a, htr145a, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                linarith only [hlam, hc012xy, hc578zy, htr014a, htr023a, htr145a, htr237a, htr378a, htr458a])
              obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr567c, htr579a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc012xy, hc789yz, htr014a, htr023a, htr148a, htr237a, htr379a, htr489a])
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
                linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
            ·
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd01a, hd56b, htr015a, htr157a, htr456a, htr457a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hc356yz, htr145c, htr158a, htr368a, htr456a, htr568b])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc789yx, htr157a, htr158a, htr578c, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc012xy, hc789zy, htr014a, htr023a, htr147a, htr238a, htr389a, htr479a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hd35a, hd89b, htr157a, htr158a, htr357a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 6 8 9 (by decide) (by decide) with
                ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
              ·
                linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a]
              ·
                linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a]
          ·
            rcases m.htr 3 5 6 (by decide) (by decide) with
              ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
            ·
              rcases m.htr 2 5 6 (by decide) (by decide) with
                ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
              ·
                rcases m.htr 1 5 6 (by decide) (by decide) with
                  ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
                ·
                  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                    linarith only [hlam, htr015c, htr056a, htr156a])
                  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                    linarith only [hlam, hd01a, hd57b, htr015a, htr156a, htr456a, htr457a])
                  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc345yz, htr015c, htr057a, htr156a, htr357a, htr456a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, hc345yz, htr156a, htr157a, htr357a, htr456a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
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
                            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                              linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc345yz, htr156c, htr168a, htr356b, htr368a, htr456a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                              linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr467a, htr468a])
                            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a]
                            ·
                              linarith only [hlam, hd01a, hd67b, htr015a, htr157a, htr578a, htr678a]
                          ·
                            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                              linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                              linarith only [hlam, hc012xy, hc678xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr568a])
                            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                              linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                              linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
                            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc012xy, hc467zy, htr017a, htr023a, htr178a, htr236a, htr367a, htr478a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc345yz, htr157c, htr178a, htr357b, htr378a, htr457a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
                            ·
                              linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
                        ·
                          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                            linarith only [hlam, htr025b, htr0510a, htr235b, htr3510a])
                          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                            linarith only [hlam, htr0510c, htr056b, htr0610b])
                          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, htr0510c, htr057b, htr0710b])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                            linarith only [hlam, hc345yz, htr016c, htr0610a, htr156c, htr356b, htr3610a, htr456a])
                          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                            linarith only [hlam, hc345yz, htr057c, htr0710a, htr357b, htr3710a, htr457a])
                          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc012xy, hc6710yx, htr015a, htr023a, htr156a, htr236a, htr3610a, htr567a])
                          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                            linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                          rcases m.htr 6 7 10 (by decide) (by decide) with
                            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                          ·
                            linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr3710a, htr6710a]
                          ·
                            linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
                      ·
                        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                          linarith only [hlam, htr025b, htr059a, htr235b, htr359a])
                        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                          linarith only [hlam, htr056b, htr059c, htr069b])
                        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057b, htr059c, htr079b])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                          linarith only [hlam, hc345yz, htr016c, htr069a, htr156c, htr356b, htr369a, htr456a])
                        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc345yz, htr057c, htr079a, htr357b, htr379a, htr457a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc012xy, hc679yx, htr015a, htr023a, htr156a, htr236a, htr369a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                          linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                        rcases m.htr 6 7 9 (by decide) (by decide) with
                          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                        ·
                          linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr379a, htr679a]
                        ·
                          linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a]
                    ·
                      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                        linarith only [hlam, htr025b, htr058a, htr235b, htr358a])
                      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, htr056b, htr058c, htr068b])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, htr057b, htr058c, htr078b])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc345yz, htr016c, htr068a, htr156c, htr356b, htr368a, htr456a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc345yz, htr057c, htr078a, htr357b, htr378a, htr457a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
                      ·
                        linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, htr025b, htr057a, htr235b, htr357a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, htr056b, htr057c, htr067b])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, hc012xy, htr015a, htr023a, htr157a, htr235a, htr357a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                      linarith only [hlam, hc345yz, htr016c, htr067a, htr156c, htr356b, htr367a, htr456a])
                    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc012xy, hc678xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                      linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc012xy, hc457zy, htr017a, htr023a, htr178a, htr235a, htr357a, htr478a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd45b, hd67a, htr156a, htr157c, htr178a, htr456a, htr678a]
                    ·
                      linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
                ·
                  rcases m.htr 0 5 6 (by decide) (by decide) with
                    ⟨htr056a, htr056b, htr056c, _, _⟩ | ⟨htr056a, htr056b, htr056c, _, _⟩
                  ·
                    rcases m.htr 5 6 7 (by decide) (by decide) with
                      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                    ·
                      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yx, htr014a, htr023a, htr146a, htr236a, htr368a, htr467a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc012xy, hc679yx, htr014a, htr023a, htr146a, htr236a, htr369a, htr467a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr369a, htr456a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012xy, hc689zy, htr014a, htr023a, htr146a, htr238a, htr389a, htr469a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd01a, hd89b, htr014a, htr146a, htr468a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a]
                      ·
                        linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
                    ·
                      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc012xy, hc678xy, htr014a, htr023a, htr146a, htr236a, htr367a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc012xy, hc679xy, htr014a, htr023a, htr146a, htr236a, htr367a, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr369a, htr456a, htr569a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc012xy, hc689yz, htr014a, htr023a, htr148a, htr236a, htr369a, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
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
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yx, htr014a, htr023a, htr146a, htr236a, htr368a, htr467a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc012xy, hc679yx, htr014a, htr023a, htr146a, htr236a, htr369a, htr467a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr369a, htr456a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012xy, hc689zy, htr014a, htr023a, htr146a, htr238a, htr389a, htr469a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd01a, hd89b, htr014a, htr146a, htr468a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a]
                      ·
                        linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
                    ·
                      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc012xy, hc678xy, htr014a, htr023a, htr146a, htr236a, htr367a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc012xy, hc679xy, htr014a, htr023a, htr146a, htr236a, htr367a, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc345yz, htr356b, htr369a, htr456a, htr569a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc012xy, hc689yz, htr014a, htr023a, htr148a, htr236a, htr369a, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
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
                  linarith only [hlam, htr025b, htr056a, htr256a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hd12b, hd57a, htr125a, htr256a, htr356a, htr357a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                rcases m.htr 4 5 7 (by decide) (by decide) with
                  ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, htr015c, htr057a, htr145c, htr457a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, htr056c, htr057b, htr067c])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hc012xy, htr014a, htr025a, htr145a, htr257a, htr457a])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                    linarith only [hlam, hc345yz, htr026b, htr067a, htr256b, htr356a, htr456c, htr467a])
                  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc012xy, hc678yx, htr014a, htr025a, htr146a, htr256a, htr467a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc012xy, hc357yz, htr014a, htr027a, htr145a, htr278a, htr378a, htr457a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a]
                  ·
                    linarith only [hlam, hd35a, hd67b, htr256a, htr257b, htr278a, htr356a, htr678a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc345yz, htr025b, htr057a, htr256a, htr356a, htr457a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hc345yz, htr256a, htr257a, htr356a, htr457a])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  rcases m.htr 4 5 8 (by decide) (by decide) with
                    ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, htr015c, htr058a, htr145c, htr458a])
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
                      linarith only [hlam, hc345yz, htr026b, htr068a, htr256b, htr356a, htr456c, htr468a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc345yz, htr057b, htr078a, htr357a, htr457c, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc012xy, hc678xy, htr014a, htr025a, htr146a, htr256a, htr468a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a]
                    ·
                      linarith only [hlam, hd01a, hd67b, htr014a, htr147a, htr478a, htr678a]
                  ·
                    rcases m.htr 4 5 9 (by decide) (by decide) with
                      ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                    ·
                      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                        linarith only [hlam, htr015c, htr059a, htr145c, htr459a])
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
                        linarith only [hlam, hc345yz, htr026b, htr069a, htr256b, htr356a, htr456c, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hc345yz, htr057b, htr079a, htr357a, htr457c, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc012xy, hc679xy, htr014a, htr025a, htr146a, htr256a, htr469a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                      rcases m.htr 6 7 9 (by decide) (by decide) with
                        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd79b, htr014a, htr146a, htr467a, htr679a]
                      ·
                        linarith only [hlam, hd01a, hd67b, htr014a, htr147a, htr479a, htr679a]
                    ·
                      rcases m.htr 4 5 10 (by decide) (by decide) with
                        ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                      ·
                        have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                          linarith only [hlam, htr015c, htr0510a, htr145c, htr4510a])
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
                          linarith only [hlam, hc345yz, htr026b, htr0610a, htr256b, htr356a, htr456c, htr4610a])
                        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                          linarith only [hlam, hc345yz, htr057b, htr0710a, htr357a, htr457c, htr4710a])
                        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc012xy, hc6710xy, htr014a, htr025a, htr146a, htr256a, htr4610a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        rcases m.htr 6 7 10 (by decide) (by decide) with
                          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                        ·
                          linarith only [hlam, hd01a, hd710b, htr014a, htr146a, htr467a, htr6710a]
                        ·
                          linarith only [hlam, hd01a, hd67b, htr014a, htr147a, htr4710a, htr6710a]
                      ·
                        rcases m.htr 5 6 7 (by decide) (by decide) with
                          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                        ·
                          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                            linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                            linarith only [hlam, hc012xy, hc678yx, htr014a, htr025a, htr146a, htr256a, htr467a, htr568a])
                          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                            linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                            linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hc012xy, hc367yz, htr014a, htr027a, htr146a, htr278a, htr378a, htr467a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc345yz, htr257b, htr278a, htr357a, htr457c, htr478a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          rcases m.htr 6 7 8 (by decide) (by decide) with
                            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                          ·
                            linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a]
                          ·
                            linarith only [hlam, hd01a, hd67b, htr014a, htr147a, htr478a, htr678a]
                        ·
                          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                            linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                            linarith only [hlam, hc012xy, hc678xy, htr014a, htr025a, htr146a, htr256a, htr468a, htr567a])
                          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                            linarith only [hlam, hc345yz, htr256b, htr268a, htr356a, htr456c, htr468a])
                          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr367a, htr368a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          rcases m.htr 6 7 8 (by decide) (by decide) with
                            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                          ·
                            linarith only [hlam, hd12b, hd67a, htr125a, htr257a, htr578a, htr678a]
                          ·
                            linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a]
            ·
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hc012xy, hc567xy, htr014a, htr023a, htr145a, htr235a, htr356a, htr457a])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd12b, hd67a, htr123a, htr235a, htr356a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd12b, hd68a, htr123a, htr235a, htr356a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              rcases m.htr 4 6 7 (by decide) (by decide) with
                ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
              ·
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hc012xy, hc567yz, htr014a, htr023a, htr146a, htr235a, htr357a, htr467a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hd12b, hd56a, htr125a, htr257a, htr356a, htr357a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr578a, htr678a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc567xy, htr356a, htr357b, htr378a, htr578a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                  linarith only [hlam, hc456zy, htr235b, htr258a, htr356a, htr468a, htr568c])
                obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc789xy, htr257a, htr258a, htr578b, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc567xy, htr356a, htr357b, htr379a, htr579a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc012xy, hc789yz, htr014a, htr023a, htr148a, htr237a, htr379a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd45b, hd89a, htr257a, htr258a, htr457a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a]
                ·
                  linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a]
              ·
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd12b, hd78a, htr123a, htr235a, htr357a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd12b, hd79a, htr123a, htr235a, htr357a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hc012xy, hc578yz, htr014a, htr023a, htr147a, htr235a, htr358a, htr478a])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc012xy, hc789zy, htr014a, htr023a, htr147a, htr238a, htr389a, htr479a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc568xy, htr356a, htr358b, htr389a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
                ·
                  linarith only [hlam, hd56a, hd78b, htr356a, htr358a, htr589a, htr789a]
        ·
          have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
            linarith only [hlam, htr1410c, htr145b, htr1510b])
          obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
            linarith only [hlam, htr1410c, htr146b, htr1610b])
          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
            linarith only [hlam, htr1410c, htr147b, htr1710b])
          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
          have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
            linarith only [hlam, htr145c, htr1510a, htr4510a])
          obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
          have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
            linarith only [hlam, hc345yz, htr1410a, htr145a, htr3510a, htr4510b])
          obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc5610yx, htr1410a, htr145a, htr4510b, htr456a])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, htr146c, htr1610a, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, hc346yz, htr1410a, htr146a, htr3610a, htr4610b])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc6710yx, htr1410a, htr146a, htr4610b, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, htr147c, htr1710a, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc456zy, htr1410a, htr146a, htr4610b, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd12b, hd610a, htr123a, htr235a, htr356a, htr5610a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd46b, hd510a, htr3510a, htr356a, htr467a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd45b, hd610a, htr3610a, htr367a, htr456a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hc467zy, htr1410a, htr147a, htr4710b, htr6710a]
          ·
            linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
      ·
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr145b, htr149c, htr159b])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, htr146b, htr149c, htr169b])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, htr147b, htr149c, htr179b])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, htr145c, htr159a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc345yz, htr145a, htr149a, htr359a, htr459b])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc569yx, htr145a, htr149a, htr456a, htr459b])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr146c, htr169a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc346yz, htr146a, htr149a, htr369a, htr469b])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc679yx, htr146a, htr149a, htr467a, htr469b])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, htr147c, htr179a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc456zy, htr146a, htr149a, htr469b, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd12b, hd69a, htr123a, htr235a, htr356a, htr569a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd46b, hd59a, htr356a, htr359a, htr467a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd45b, hd69a, htr367a, htr369a, htr456a, htr567a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc467zy, htr147a, htr149a, htr479b, htr679a]
        ·
          linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a]
    ·
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr145b, htr148c, htr158b])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr146b, htr148c, htr168b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr147b, htr148c, htr178b])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, htr145c, htr158a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc345yz, htr145a, htr148a, htr358a, htr458b])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc568yx, htr145a, htr148a, htr456a, htr458b])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr146c, htr168a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc346yz, htr146a, htr148a, htr368a, htr468b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc678yx, htr146a, htr148a, htr467a, htr468b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, htr147c, htr178a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc456zy, htr146a, htr148a, htr468b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr123a, htr235a, htr356a, htr568a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd46b, hd58a, htr356a, htr358a, htr467a, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr367a, htr368a, htr456a, htr567a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hc467zy, htr147a, htr148a, htr478b, htr678a]
      ·
        linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
  ·
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr145b, htr147c, htr157b])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr146b, htr147c, htr167b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, htr145c, htr157a, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc345yz, htr145a, htr147a, htr357a, htr457b])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc567yx, htr145a, htr147a, htr456a, htr457b])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr146c, htr167a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc346yz, htr146a, htr147a, htr367a, htr467b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc678xy, htr146a, htr147a, htr467b, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hc679xy, htr146a, htr147a, htr467b, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hc6710xy, htr146a, htr147a, htr4610a, htr467b])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc456zy, htr146a, htr147a, htr467b, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr123a, htr235a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd46b, hd57a, htr356a, htr357a, htr468a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr367a, htr368a, htr456a, htr568a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hd46b, hd57a, htr356a, htr357a, htr469a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr367a, htr369a, htr456a, htr569a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
      linarith only [hlam, hd46b, hd57a, htr356a, htr357a, htr4610a, htr5610a])
    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr3610a, htr367a, htr456a, htr5610a])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr123a, htr235a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd45b, hd57a, htr145a, htr147a, htr478a, htr578a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc457yx, htr145a, htr147c, htr178a, htr478a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd12b, hd79a, htr123a, htr235a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd45b, hd57a, htr145a, htr147a, htr479a, htr579a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc457yx, htr145a, htr147c, htr179a, htr479a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd12b, hd910a, htr123a, htr236a, htr369a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, hc012xy, hc689yz, htr017a, htr023a, htr178a, htr236a, htr369a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hc012xy, hc6910yz, htr017a, htr023a, htr179a, htr236a, htr3610a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
    ·
      linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_225 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_225 m htr014a htr015a htr015c htr016a htr016c htr017a htr023a htr025a htr025b htr026b htr027a htr123a htr125a htr126a htr145a htr145b htr145c htr146a htr146b htr146c htr235a htr235b htr236a htr237a htr238a

#print axioms shard_225
end Jsp404.NoSatElevenDBMTerminal
