import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_104 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr037c : m.d 0 7 < m.d 0 3)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
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
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr024c, htr045a, htr245a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc012yz, htr024a, htr124c, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr024c, htr046a, htr246a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    rcases m.htr 2 4 7 (by decide) (by decide) with
      ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
    ·
      rcases m.htr 2 4 8 (by decide) (by decide) with
        ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
      ·
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr056a, htr123a, htr245a, htr456a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd02a, hd67b, htr024a, htr245a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd02a, hd68b, htr024a, htr245a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc012yz, hc567zy, htr024a, htr123a, htr236a, htr245a, htr367a, htr457a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, hc012yz, hc356yz, htr023c, htr024a, htr036c, htr067a, htr123a, htr245a, htr367a, htr456a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                  linarith only [hlam, hc012yz, htr025b, htr058a, htr123a, htr235c, htr258a])
                obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                  linarith only [hlam, hd02a, hd56b, htr025a, htr258a, htr456a, htr458a])
                obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc012yz, hc578zy, htr024a, htr123a, htr237a, htr245a, htr378a, htr458a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd02a, hd78b, htr024a, htr245a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a]
                ·
                  linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a]
              ·
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hd02a, hd56b, htr025a, htr257a, htr456a, htr457a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc012yz, htr025b, htr057a, htr123a, htr235c, htr257a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc012yz, hc356yz, htr023c, htr024a, htr036c, htr068a, htr123a, htr245a, htr368a, htr456a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc012yz, hc678yz, htr024a, htr123a, htr236a, htr247a, htr368a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a]
                ·
                  linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
            ·
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                rcases m.htr 2 5 6 (by decide) (by decide) with
                  ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
                ·
                  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                    linarith only [hlam, htr025c, htr056a, htr256a])
                  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                    linarith only [hlam, hc012yz, htr025a, htr125c, htr156a, htr256a])
                  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                    linarith only [hlam, hd02a, hd57b, htr025a, htr256a, htr456a, htr457a])
                  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc345yz, htr025c, htr057a, htr256a, htr357a, htr456a])
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
                              linarith only [hlam, hc012yz, hc678yx, htr025a, htr123a, htr236a, htr256a, htr368a, htr567a])
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
                              linarith only [hlam, hc012yz, hc678zy, htr024a, htr123a, htr237a, htr246a, htr378a, htr468a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd02a, hd78b, htr025a, htr256a, htr567a, htr678a]
                            ·
                              linarith only [hlam, hd01a, hd67b, htr015a, htr157a, htr578a, htr678a]
                          ·
                            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                              linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                              linarith only [hlam, hc012yz, hc678xy, htr025a, htr123a, htr236a, htr256a, htr367a, htr568a])
                            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                              linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                              linarith only [hlam, hc012yz, hc678yz, htr024a, htr123a, htr236a, htr247a, htr368a, htr478a])
                            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc012yz, hc467zy, htr027a, htr123a, htr127b, htr178a, htr236a, htr367a, htr478a])
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
                            linarith only [hlam, htr035b, htr0510a, htr3510a])
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
                            linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr036c, htr0610a, htr123a, htr256a, htr356b, htr3610a, htr456a])
                          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                            linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr037c, htr0710a, htr123a, htr256a, htr357b, htr3710a, htr456a])
                          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc012yz, hc6710yx, htr025a, htr123a, htr236a, htr256a, htr3610a, htr567a])
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
                          linarith only [hlam, htr035b, htr059a, htr359a])
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
                          linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr036c, htr069a, htr123a, htr256a, htr356b, htr369a, htr456a])
                        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr037c, htr079a, htr123a, htr256a, htr357b, htr379a, htr456a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc012yz, hc679yx, htr025a, htr123a, htr236a, htr256a, htr369a, htr567a])
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
                        linarith only [hlam, htr035b, htr058a, htr358a])
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
                        linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr036c, htr068a, htr123a, htr256a, htr356b, htr368a, htr456a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr037c, htr078a, htr123a, htr256a, htr357b, htr378a, htr456a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc012yz, hc678yx, htr025a, htr123a, htr236a, htr256a, htr368a, htr567a])
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
                      linarith only [hlam, htr035b, htr057a, htr357a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, htr056b, htr057c, htr067b])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, htr015c, htr035b, htr157a, htr357a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                      linarith only [hlam, hc012yz, hc345yz, htr023c, htr025a, htr036c, htr067a, htr123a, htr256a, htr356b, htr367a, htr456a])
                    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc012yz, hc678xy, htr025a, htr123a, htr236a, htr256a, htr367a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                      linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
                    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc012yz, hc678yz, htr024a, htr123a, htr236a, htr247a, htr368a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc012yz, hc457zy, htr027a, htr123a, htr127b, htr178a, htr235a, htr357a, htr478a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd45b, hd67a, htr156a, htr157c, htr178a, htr456a, htr678a]
                    ·
                      linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
                ·
                  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                    linarith only [hlam, hc012yz, htr025b, htr056a, htr123a, htr235c, htr256a])
                  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hd12b, hd57a, htr123a, htr235c, htr256a, htr356a, htr357a])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  rcases m.htr 4 5 7 (by decide) (by decide) with
                    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr057a, htr123a, htr245a, htr457a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, htr056c, htr057b, htr067c])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc345yz, htr056b, htr067a, htr356a, htr456c, htr467a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc012yz, hc678yx, htr024a, htr123a, htr235c, htr246a, htr256a, htr467a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc012yz, hc678zy, htr024a, htr123a, htr237a, htr246a, htr378a, htr468a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc012yz, hc357yz, htr023c, htr024a, htr037c, htr078a, htr123a, htr245a, htr378a, htr457a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd02a, hd78b, htr024a, htr246a, htr467a, htr678a]
                    ·
                      linarith only [hlam, hd35a, hd67b, htr056a, htr057b, htr078a, htr356a, htr678a]
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc345yz, htr056a, htr057a, htr356a, htr457a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    rcases m.htr 4 5 8 (by decide) (by decide) with
                      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                    ·
                      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                        linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr058a, htr123a, htr245a, htr458a])
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
                        linarith only [hlam, hc345yz, htr056b, htr068a, htr356a, htr456c, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc345yz, htr057b, htr078a, htr357a, htr457c, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc012yz, hc678xy, htr024a, htr123a, htr235c, htr246a, htr256a, htr468a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        linarith only [hlam, hd02a, hd78b, htr024a, htr246a, htr467a, htr678a]
                      ·
                        linarith only [hlam, hd02a, hd67b, htr024a, htr247a, htr478a, htr678a]
                    ·
                      rcases m.htr 4 5 9 (by decide) (by decide) with
                        ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                      ·
                        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                          linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr059a, htr123a, htr245a, htr459a])
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
                          linarith only [hlam, hc345yz, htr056b, htr069a, htr356a, htr456c, htr469a])
                        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hc345yz, htr057b, htr079a, htr357a, htr457c, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc012yz, hc679xy, htr024a, htr123a, htr235c, htr246a, htr256a, htr469a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        rcases m.htr 6 7 9 (by decide) (by decide) with
                          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                        ·
                          linarith only [hlam, hd02a, hd79b, htr024a, htr246a, htr467a, htr679a]
                        ·
                          linarith only [hlam, hd02a, hd67b, htr024a, htr247a, htr479a, htr679a]
                      ·
                        rcases m.htr 4 5 10 (by decide) (by decide) with
                          ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                        ·
                          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                            linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr0510a, htr123a, htr245a, htr4510a])
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
                            linarith only [hlam, hc345yz, htr056b, htr0610a, htr356a, htr456c, htr4610a])
                          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                            linarith only [hlam, hc345yz, htr057b, htr0710a, htr357a, htr457c, htr4710a])
                          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc012yz, hc6710xy, htr024a, htr123a, htr235c, htr246a, htr256a, htr4610a, htr567a])
                          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                            linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                          rcases m.htr 6 7 10 (by decide) (by decide) with
                            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                          ·
                            linarith only [hlam, hd02a, hd710b, htr024a, htr246a, htr467a, htr6710a]
                          ·
                            linarith only [hlam, hd02a, hd67b, htr024a, htr247a, htr4710a, htr6710a]
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
                              linarith only [hlam, hc012yz, hc678yx, htr024a, htr123a, htr235c, htr246a, htr256a, htr467a, htr568a])
                            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                              linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc012yz, hc678zy, htr024a, htr123a, htr237a, htr246a, htr378a, htr468a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                              linarith only [hlam, hc012yz, hc367yz, htr023c, htr024a, htr037c, htr078a, htr123a, htr246a, htr378a, htr467a])
                            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                              linarith only [hlam, hc345yz, htr057b, htr078a, htr357a, htr457c, htr478a])
                            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd02a, hd78b, htr024a, htr246a, htr467a, htr678a]
                            ·
                              linarith only [hlam, hd02a, hd67b, htr024a, htr247a, htr478a, htr678a]
                          ·
                            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                              linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
                            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                              linarith only [hlam, hc012yz, hc678xy, htr024a, htr123a, htr235c, htr246a, htr256a, htr468a, htr567a])
                            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                              linarith only [hlam, hc345yz, htr056b, htr068a, htr356a, htr456c, htr468a])
                            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                              linarith only [hlam, hd12b, hd67a, htr023c, htr036c, htr068a, htr123a, htr367a, htr368a])
                            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                              linarith only [hlam, hc012yz, hc678yz, htr024a, htr123a, htr236a, htr247a, htr368a, htr478a])
                            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd12b, hd67a, htr023c, htr035c, htr057a, htr123a, htr578a, htr678a]
                            ·
                              linarith only [hlam, hd12b, hd78a, htr123a, htr235c, htr256a, htr567a, htr678a]
              ·
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, htr015c, htr035b, htr156a, htr356a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
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
                    linarith only [hlam, hc012yz, hc567yz, htr024a, htr123a, htr235a, htr246a, htr357a, htr467a])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hd12b, hd56a, htr123a, htr235c, htr257a, htr356a, htr357a])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc012yz, htr025a, htr125c, htr157a, htr257a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc012yz, hc456zy, htr026a, htr123a, htr126b, htr168a, htr235a, htr356a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc012yz, hc678zy, htr024a, htr123a, htr237a, htr246a, htr378a, htr468a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc567xy, htr356a, htr357b, htr378a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd02a, hd78b, htr024a, htr246a, htr467a, htr678a]
                  ·
                    linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr578a, htr678a]
                ·
                  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                    linarith only [hlam, hc012yz, hc456zy, htr026a, htr123a, htr126b, htr167a, htr235a, htr356a, htr467a])
                  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hc568xy, htr156c, htr158a, htr167a, htr567a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc012yz, htr025a, htr125c, htr158a, htr258a])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                    linarith only [hlam, hd12b, hd56a, htr123a, htr235c, htr258a, htr356a, htr358a])
                  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc012yz, hc578yz, htr024a, htr123a, htr235a, htr247a, htr358a, htr478a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd12b, hd78a, htr123a, htr235a, htr357a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a]
                  ·
                    linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a]
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, hc012yz, htr024b, htr0410a, htr124a, htr2410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr0410c, htr045b, htr0510b])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410c, htr046b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr0510a, htr123a, htr245a, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
              linarith only [hlam, hc345yz, htr2410a, htr245a, htr3510a, htr4510b])
            obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hc5610yx, htr124b, htr145a, htr2410a, htr4510b, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc4510yx, htr0410a, htr045b, htr056a, htr456a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd12b, hd510a, htr023c, htr035c, htr056a, htr123a, htr3510a, htr356a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hc012yz, htr023c, htr024a, htr036c, htr0610a, htr123a, htr246a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            rcases m.htr 5 6 10 (by decide) (by decide) with
              ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            ·
              linarith only [hlam, hc456zy, htr2410a, htr246a, htr4610b, htr5610a]
            ·
              linarith only [hlam, hd12b, hd610a, htr123a, htr235a, htr356a, htr5610a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc012yz, htr024b, htr049a, htr124a, htr249a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045b, htr049c, htr059b])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046b, htr049c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr059a, htr123a, htr245a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, hc345yz, htr245a, htr249a, htr359a, htr459b])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569yx, htr124b, htr145a, htr249a, htr456a, htr459b])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc459yx, htr045b, htr049a, htr056a, htr456a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd12b, hd59a, htr023c, htr035c, htr056a, htr123a, htr356a, htr359a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc012yz, htr023c, htr024a, htr036c, htr069a, htr123a, htr246a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hc456zy, htr246a, htr249a, htr469b, htr569a]
          ·
            linarith only [hlam, hd12b, hd69a, htr123a, htr235a, htr356a, htr569a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc012yz, htr024b, htr048a, htr124a, htr248a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr045b, htr048c, htr058b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046b, htr048c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr058a, htr123a, htr245a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc345yz, htr245a, htr248a, htr358a, htr458b])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc568yx, htr124b, htr145a, htr248a, htr456a, htr458b])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc458yx, htr045b, htr048a, htr056a, htr456a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd12b, hd58a, htr023c, htr035c, htr056a, htr123a, htr356a, htr358a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012yz, htr023c, htr024a, htr036c, htr068a, htr123a, htr246a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hc456zy, htr246a, htr248a, htr468b, htr568a]
        ·
          linarith only [hlam, hd12b, hd68a, htr123a, htr235a, htr356a, htr568a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc012yz, htr024b, htr047a, htr124a, htr247a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045b, htr047c, htr057b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046b, htr047c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr057a, htr123a, htr245a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc345yz, htr245a, htr247a, htr357a, htr457b])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc567yx, htr124b, htr145a, htr247a, htr456a, htr457b])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd12b, hd57a, htr023c, htr035c, htr056a, htr123a, htr356a, htr357a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc012yz, htr023c, htr024a, htr036c, htr067a, htr123a, htr246a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        linarith only [hlam, hc456zy, htr246a, htr247a, htr467b, htr567a]
      ·
        linarith only [hlam, hd12b, hd67a, htr123a, htr235a, htr356a, htr567a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc012yz, htr024b, htr046a, htr124a, htr246a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045b, htr046c, htr056b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr124b, htr146a, htr246a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc012yz, htr023c, htr024a, htr035c, htr056a, htr123a, htr245a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc345yz, htr245a, htr246a, htr356a, htr456b])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr124b, htr145a, htr246a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc456yx, htr045b, htr046a, htr057a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr023c, htr035c, htr057a, htr123a, htr356a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr124b, htr145a, htr246a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
      linarith only [hlam, hc456yx, htr045b, htr046a, htr058a, htr458a])
    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr023c, htr035c, htr058a, htr123a, htr356a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569xy, htr124b, htr145a, htr246a, htr456b, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr059a, htr059b, htr059c, _, _⟩
      linarith only [hlam, hc456yx, htr045b, htr046a, htr059a, htr459a])
    obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr023c, htr035c, htr059a, htr123a, htr356a, htr359a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr123a, htr235a, htr356a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr124a, htr246a, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc456yx, htr145a, htr146c, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr123a, htr235a, htr356a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr124a, htr246a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc456yx, htr145a, htr146c, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr123a, htr235a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd12b, hd89a, htr123a, htr235a, htr358a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hc012yz, hc578yz, htr026a, htr123a, htr126b, htr167a, htr235a, htr358a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc012yz, hc589yz, htr026a, htr123a, htr126b, htr168a, htr235a, htr359a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
    ·
      linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]

theorem shard_104 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr037c : m.d 0 7 < m.d 0 3)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_104 m htr015a htr015c htr016a htr023c htr024a htr024b htr024c htr025a htr025b htr025c htr026a htr027a htr035b htr035c htr036c htr037c htr123a htr124a htr124b htr124c htr125c htr126b htr127b htr235a htr235c htr236a htr237a htr245a

#print axioms shard_104
end Jsp404.NoSatElevenDBMTerminal
