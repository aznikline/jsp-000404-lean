import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_381 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr1310a : m.d 1 3 + lam ≤ m.d 3 10)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd17a := (m.hrange 1 7 (by decide)).1
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < 4*lam := by
    linarith only [hd38braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
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
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  rcases m.htr 2 3 6 (by decide) (by decide) with
    ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
  ·
    rcases m.htr 2 3 7 (by decide) (by decide) with
      ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
    ·
      rcases m.htr 2 3 8 (by decide) (by decide) with
        ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
      ·
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hd14b, hd45a, htr014a, htr015a, htr156a, htr456a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc145yx, htr014a, htr015c, htr056a, htr156a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc124xy, hc567yx, htr014a, htr015a, htr123a, htr157a, htr235a, htr356a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc124xy, hc568yx, htr014a, htr015a, htr123a, htr158a, htr235a, htr356a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd12a, hd67b, htr123a, htr235a, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd12a, hd68b, htr123a, htr235a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hc456yz, htr356a, htr357a, htr467a, htr567b])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd12a, hd78b, htr123a, htr235a, htr357a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd12a, hd79b, htr123a, htr235a, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr178a, htr467b, htr567a, htr678a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                    linarith only [hlam, hc124xy, hc578zy, htr014a, htr017a, htr123a, htr178a, htr235a, htr358a])
                  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc456yz, htr147b, htr179a, htr467b, htr567a, htr679a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc124xy, hc789yz, htr014a, htr017a, htr123a, htr179a, htr238a, htr389a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc145yx, hc378zy, htr014a, htr017a, htr158a, htr178a, htr389a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd56b, hd78a, htr356a, htr358a, htr589a, htr789a]
                  ·
                    linarith only [hlam, hd14b, hd89a, htr014a, htr017a, htr178a, htr789a]
                ·
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hc124xy, hc567zy, htr014a, htr016a, htr123a, htr146b, htr235a, htr357a, htr467a])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hd12a, hd56b, htr125a, htr257a, htr356a, htr357a])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd14b, hd78a, htr014a, htr016a, htr146b, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr578a, htr678a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc145yx, hc367zy, htr014a, htr016a, htr146b, htr157a, htr378a, htr467a, htr578a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hc124xy, hc678yz, htr014a, htr016a, htr123a, htr168a, htr237a, htr378a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc124xy, hc789yx, htr014a, htr017a, htr123a, htr179a, htr237a, htr378a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc156yz, htr168a, htr235c, htr258a, htr356a, htr568b])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd17a, hd56b, htr179a, htr356a, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc145yx, hc367zy, htr014a, htr016a, htr146b, htr157a, htr379a, htr467a, htr579a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc124xy, hc789zy, htr014a, htr018a, htr123a, htr189a, htr237a, htr379a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd15a, hd89b, htr157a, htr257a, htr258a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 6 8 9 (by decide) (by decide) with
                    ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                  ·
                    linarith only [hlam, hc156yz, htr168a, htr568c, htr589a, htr689a]
                  ·
                    linarith only [hlam, hc156yz, htr168b, htr189a, htr568a, htr689a]
              ·
                rcases m.htr 2 5 6 (by decide) (by decide) with
                  ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
                ·
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hd12a, hd57b, htr125a, htr256a, htr356a, htr357a])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  rcases m.htr 4 5 7 (by decide) (by decide) with
                    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc345zy, htr056a, htr057a, htr356a, htr457a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                      linarith only [hlam, hc345zy, htr256a, htr257a, htr356a, htr457a])
                    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                    rcases m.htr 4 5 8 (by decide) (by decide) with
                      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                    ·
                      rcases m.htr 4 5 9 (by decide) (by decide) with
                        ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                      ·
                        rcases m.htr 4 5 10 (by decide) (by decide) with
                          ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                        ·
                          rcases m.htr 5 6 7 (by decide) (by decide) with
                            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                          ·
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc124xy, hc678yx, htr014a, htr016a, htr125a, htr168a, htr256a, htr567a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                              linarith only [hlam, hc345zy, htr146b, htr168a, htr256c, htr268a, htr356a, htr456b])
                            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                              linarith only [hlam, hc345zy, htr356c, htr367a, htr456a, htr567a])
                            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                              linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr367a, htr368a])
                            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc124xy, hc678zy, htr014a, htr017a, htr123a, htr178a, htr236a, htr368a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hc345zy, htr147b, htr178a, htr357a, htr457b, htr578a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd12a, hd78b, htr125a, htr256a, htr567a, htr678a]
                            ·
                              linarith only [hlam, hd12a, hd67b, htr125a, htr257a, htr578a, htr678a]
                          ·
                            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                              linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr567a])
                            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                              linarith only [hlam, hc124xy, hc678xy, htr014a, htr016a, htr125a, htr167a, htr256a, htr568a])
                            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc345zy, htr146b, htr168a, htr356a, htr456b, htr568a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc124xy, hc678yz, htr014a, htr016a, htr123a, htr168a, htr237a, htr378a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                              linarith only [hlam, hc124xy, hc367zy, htr014a, htr016a, htr127a, htr167a, htr278a, htr378a])
                            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc345zy, htr147b, htr178a, htr257c, htr278a, htr357a, htr457b])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd14b, hd67a, htr014a, htr017a, htr178a, htr678a]
                            ·
                              linarith only [hlam, hd14b, hd78a, htr014a, htr016a, htr167a, htr678a]
                        ·
                          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                            linarith only [hlam, htr045b, htr0510a, htr4510a])
                          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                            linarith only [hlam, htr0510c, htr056b, htr0610b])
                          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, htr0510c, htr057b, htr0710b])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                            linarith only [hlam, hc146yx, htr014a, htr016c, htr0610a, htr1610a])
                          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
                          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                            linarith only [hlam, hc147yx, htr014a, htr017c, htr0710a, htr1710a])
                          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc124xy, hc6710yx, htr014a, htr016a, htr125a, htr1610a, htr256a, htr567a])
                          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                            linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr567a])
                          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                          rcases m.htr 6 7 10 (by decide) (by decide) with
                            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                          ·
                            linarith only [hlam, hd14b, hd67a, htr014a, htr017a, htr1710a, htr6710a]
                          ·
                            linarith only [hlam, hd14b, hd710a, htr014a, htr016a, htr167a, htr6710a]
                      ·
                        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                          linarith only [hlam, htr045b, htr059a, htr459a])
                        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                          linarith only [hlam, htr056b, htr059c, htr069b])
                        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057b, htr059c, htr079b])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                          linarith only [hlam, hc146yx, htr014a, htr016c, htr069a, htr169a])
                        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc147yx, htr014a, htr017c, htr079a, htr179a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc124xy, hc679yx, htr014a, htr016a, htr125a, htr169a, htr256a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr567a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        rcases m.htr 6 7 9 (by decide) (by decide) with
                          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                        ·
                          linarith only [hlam, hd14b, hd67a, htr014a, htr017a, htr179a, htr679a]
                        ·
                          linarith only [hlam, hd14b, hd79a, htr014a, htr016a, htr167a, htr679a]
                    ·
                      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                        linarith only [hlam, htr045b, htr058a, htr458a])
                      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, htr056b, htr058c, htr068b])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, htr057b, htr058c, htr078b])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                        linarith only [hlam, hc146yx, htr014a, htr016c, htr068a, htr168a])
                      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc147yx, htr014a, htr017c, htr078a, htr178a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc124xy, hc678yx, htr014a, htr016a, htr125a, htr168a, htr256a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                        linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr567a])
                      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        linarith only [hlam, hd14b, hd67a, htr014a, htr017a, htr178a, htr678a]
                      ·
                        linarith only [hlam, hd14b, hd78a, htr014a, htr016a, htr167a, htr678a]
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, htr045b, htr057a, htr457a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, htr056b, htr057c, htr067b])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                      linarith only [hlam, hc146yx, htr014a, htr016c, htr067a, htr167a])
                    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                      linarith only [hlam, htr025c, htr045b, htr257a, htr457a])
                    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc124xy, hc678xy, htr014a, htr016a, htr125a, htr167a, htr256a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc345zy, htr146b, htr168a, htr356a, htr456b, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc124xy, hc678yz, htr014a, htr016a, htr123a, htr168a, htr237a, htr378a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc124xy, hc357zy, htr014a, htr015a, htr127a, htr145b, htr278a, htr378a, htr457a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd35b, hd67a, htr256a, htr257c, htr278a, htr356a, htr678a]
                    ·
                      linarith only [hlam, hd14b, hd78a, htr014a, htr016a, htr167a, htr678a]
                ·
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                      linarith only [hlam, hc345zy, htr356c, htr367a, htr456a, htr567a])
                    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc124xy, hc678yx, htr014a, htr016a, htr123a, htr168a, htr236a, htr367a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc124xy, hc679yx, htr014a, htr016a, htr123a, htr169a, htr236a, htr367a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc345zy, htr146b, htr168a, htr356a, htr456b, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                      linarith only [hlam, hc345zy, htr356c, htr368a, htr456a, htr568a])
                    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc124xy, hc678zy, htr014a, htr017a, htr123a, htr178a, htr236a, htr368a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc345zy, htr146b, htr169a, htr356a, htr456b, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                      linarith only [hlam, hc345zy, htr356c, htr369a, htr456a, htr569a])
                    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc124xy, hc689zy, htr014a, htr018a, htr123a, htr189a, htr236a, htr369a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd12a, hd89b, htr123a, htr236a, htr368a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc167yz, htr178a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc167yz, htr178b, htr189a, htr678a, htr789a]
                  ·
                    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                      linarith only [hlam, hc345zy, htr146b, htr167a, htr356a, htr456b, htr567a])
                    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                      linarith only [hlam, hc124xy, hc678xy, htr014a, htr016a, htr123a, htr167a, htr236a, htr368a])
                    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                      linarith only [hlam, hc124xy, hc679xy, htr014a, htr016a, htr123a, htr167a, htr236a, htr369a])
                    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc345zy, htr356c, htr368a, htr456a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc345zy, htr146b, htr168a, htr356a, htr456b, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc124xy, hc678yz, htr014a, htr016a, htr123a, htr168a, htr237a, htr378a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc345zy, htr356c, htr369a, htr456a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc345zy, htr146b, htr169a, htr356a, htr456b, htr569a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                      linarith only [hlam, hc124xy, hc689yz, htr014a, htr016a, htr123a, htr169a, htr238a, htr389a])
                    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd14b, hd78a, htr014a, htr016a, htr167a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd14b, hd89a, htr014a, htr016a, htr168a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a]
            ·
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc124xy, hc567xy, htr014a, htr015a, htr123a, htr145b, htr235a, htr357a, htr456a])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd14b, hd67a, htr014a, htr015a, htr145b, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hd14b, hd56a, htr014a, htr016a, htr167a, htr567a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd14b, hd68a, htr014a, htr015a, htr145b, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hd14b, hd56a, htr014a, htr016a, htr168a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hd14b, hd56a, htr014a, htr015c, htr057a, htr456a, htr457a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc356zy, htr367a, htr456a, htr457a, htr567c])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd56a, hd67b, htr456a, htr457a, htr578a, htr678a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc567xy, htr147b, htr178a, htr456a, htr457b, htr578a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc124xy, hc678zy, htr014a, htr017a, htr123a, htr178a, htr236a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc356zy, htr045b, htr058a, htr368a, htr456a, htr568c])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc789xy, htr057a, htr058a, htr578b, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc567xy, htr147b, htr179a, htr456a, htr457b, htr579a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc124xy, hc789yz, htr014a, htr017a, htr123a, htr179a, htr238a, htr389a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd35b, hd89a, htr057a, htr058a, htr357a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc146yx, hc378zy, htr014a, htr017a, htr168a, htr178a, htr389a, htr689a]
                ·
                  linarith only [hlam, hc356zy, htr368a, htr568b, htr589a, htr689a]
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc124xy, hc567yz, htr014a, htr015a, htr123a, htr145b, htr236a, htr367a, htr457a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd14b, hd78a, htr014a, htr015a, htr145b, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd14b, hd79a, htr014a, htr015a, htr145b, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc146yx, hc357zy, htr014a, htr015a, htr145b, htr167a, htr378a, htr457a, htr678a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc124xy, hc578yz, htr014a, htr015a, htr123a, htr158a, htr237a, htr378a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc356zy, htr367a, htr567b, htr579a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc146yx, hc357zy, htr014a, htr015a, htr145b, htr167a, htr379a, htr457a, htr679a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc124xy, hc789zy, htr014a, htr018a, htr123a, htr189a, htr237a, htr379a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc568xy, htr145b, htr158b, htr189a, htr456a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd56a, hd78b, htr145b, htr158a, htr456a, htr589a, htr789a]
          ·
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc134xy, hc356zy, htr014a, htr015a, htr1310a, htr156a, htr2310a, htr236a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc145yx, htr014a, htr015c, htr056a, htr156a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc134xy, hc367zy, htr014a, htr016a, htr1310a, htr167a, htr2310a, htr237a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
              linarith only [hlam, htr2310c, htr235b, htr2510b])
            obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd13a, hd56b, htr1310a, htr2310a, htr235a, htr356a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
              linarith only [hlam, htr235c, htr2510a, htr3510a])
            obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, hc035yz, htr0510a, htr2310a, htr235a, htr3510b])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0510c, htr056b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
              linarith only [hlam, hc146yx, htr014a, htr016c, htr0610a, htr1610a])
            obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc134xy, hc6710yx, htr014a, htr016a, htr1310a, htr1610a, htr2310a, htr236b, htr267a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              linarith only [hlam, hc135yz, htr156a, htr236c, htr267a, htr356c, htr567a]
            ·
              linarith only [hlam, hc135yz, htr156b, htr167a, htr356a, htr567a]
        ·
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc134xy, hc356zy, htr014a, htr015a, htr139a, htr156a, htr236a, htr239a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc145yx, htr014a, htr015c, htr056a, htr156a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc134xy, hc367zy, htr014a, htr016a, htr139a, htr167a, htr237a, htr239a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr259a, htr259b, htr259c, _, _⟩
            linarith only [hlam, htr235b, htr239c, htr259b])
          obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd13a, hd56b, htr139a, htr235a, htr239a, htr356a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, htr235c, htr259a, htr359a])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, hc035yz, htr059a, htr235a, htr239a, htr359b])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr056b, htr059c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc146yx, htr014a, htr016c, htr069a, htr169a])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc134xy, hc679yx, htr014a, htr016a, htr139a, htr169a, htr236b, htr239a, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            linarith only [hlam, hc135yz, htr156a, htr236c, htr267a, htr356c, htr567a]
          ·
            linarith only [hlam, hc135yz, htr156b, htr167a, htr356a, htr567a]
      ·
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc134xy, hc356zy, htr014a, htr015a, htr138a, htr156a, htr236a, htr238a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc145yx, htr014a, htr015c, htr056a, htr156a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc134xy, hc367zy, htr014a, htr016a, htr138a, htr167a, htr237a, htr238a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr235b, htr238c, htr258b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd13a, hd56b, htr138a, htr235a, htr238a, htr356a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr235c, htr258a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc035yz, htr058a, htr235a, htr238a, htr358b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr058c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc146yx, htr014a, htr016c, htr068a, htr168a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc134xy, hc678yx, htr014a, htr016a, htr138a, htr168a, htr236b, htr238a, htr267a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          linarith only [hlam, hc135yz, htr156a, htr236c, htr267a, htr356c, htr567a]
        ·
          linarith only [hlam, hc135yz, htr156b, htr167a, htr356a, htr567a]
    ·
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc134xy, hc356zy, htr014a, htr015a, htr137a, htr156a, htr236a, htr237a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc145yx, htr014a, htr015c, htr056a, htr156a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr235b, htr237c, htr257b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd13a, hd56b, htr137a, htr235a, htr237a, htr356a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc357yx, htr235b, htr237a, htr256a, htr356a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr235c, htr257a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc035yz, htr057a, htr235a, htr237a, htr357b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr056b, htr057c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc146yx, htr014a, htr016c, htr067a, htr167a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc578xy, htr056a, htr057a, htr256a, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc134xy, hc678xy, htr014a, htr016a, htr137a, htr167a, htr236b, htr237a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hc134xy, hc679xy, htr014a, htr016a, htr137a, htr167a, htr236b, htr237a, htr269a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr235c, htr258a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc135yz, htr156a, htr236c, htr268a, htr356c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc135yz, htr156b, htr168a, htr356a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc134xy, hc368zy, htr014a, htr016a, htr137a, htr168a, htr237a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc035yz, htr058a, htr235a, htr238a, htr358b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc135yz, htr156a, htr236c, htr269a, htr356c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc135yz, htr156b, htr169a, htr356a, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd35b, hd78a, htr056a, htr057a, htr356a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd35b, hd89a, htr056a, htr058a, htr356a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd34b, hd58a, htr234a, htr238a, htr389a, htr589a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc134xy, hc689yz, htr014a, htr016a, htr137a, htr169a, htr378a, htr789a]
      ·
        linarith only [hlam, hc134xy, hc678yz, htr014a, htr016a, htr138a, htr168a, htr389a, htr789a]
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr235b, htr236c, htr256b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, htr235c, htr256a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc135yz, htr156a, htr235a, htr236a, htr356b])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc134xy, hc567xy, htr014a, htr015a, htr136a, htr156a, htr235b, htr236a, htr257a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc134xy, hc568xy, htr014a, htr015a, htr136a, htr156a, htr235b, htr236a, htr258a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr235c, htr257a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, htr235c, htr258a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd14b, hd67a, htr014a, htr015a, htr156a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr367a, htr567a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd14b, hd68a, htr014a, htr015a, htr156a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr368a, htr568a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc134xy, hc345zy, htr014a, htr015c, htr057a, htr136a, htr235a, htr236a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc345zy, htr235a, htr237a, htr357b, htr457a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd13a, hd78b, htr136a, htr236a, htr237a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd13a, hd79b, htr136a, htr236a, htr237a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc345zy, htr357c, htr378a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc245zy, htr147b, htr178a, htr257a, htr457b, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc134xy, hc378zy, htr014a, htr017a, htr136a, htr178a, htr236a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc035yz, htr058a, htr235a, htr238a, htr358b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc345zy, htr357c, htr379a, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc245zy, htr147b, htr179a, htr257a, htr457b, htr579a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd25b, hd89a, htr057a, htr058a, htr257a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd34b, hd58a, htr234a, htr238a, htr389a, htr589a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc134xy, hc789yz, htr014a, htr017a, htr136a, htr179a, htr368a, htr689a]
      ·
        linarith only [hlam, hc134xy, hc678zy, htr014a, htr017a, htr138a, htr178a, htr389a, htr689a]
    ·
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc134xy, hc357zy, htr014a, htr015a, htr136a, htr145b, htr236a, htr237a, htr457a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd14b, hd78a, htr014a, htr015a, htr145b, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd14b, hd79a, htr014a, htr015a, htr145b, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr379a, htr579a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc134xy, hc567yz, htr014a, htr015a, htr137a, htr145b, htr378a, htr457a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc134xy, hc578yz, htr014a, htr015a, htr136a, htr158a, htr367a, htr678a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc135yz, htr158a, htr235a, htr238a, htr358b])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr136a, htr236a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd38b, hd56a, htr156a, htr158a, htr389a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc568xy, htr156a, htr158b, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        linarith only [hlam, hc134xy, hc789zy, htr014a, htr018a, htr136a, htr189a, htr367a, htr679a]
      ·
        linarith only [hlam, hc134xy, hc567yz, htr014a, htr015a, htr137a, htr145b, htr379a, htr457a, htr679a]

theorem shard_381 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr1310a : m.d 1 3 + lam ≤ m.d 3 10)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    : False :=
  proof_shard_381 m htr014a htr015a htr015c htr016a htr016c htr017a htr017c htr018a htr025c htr045b htr123a htr125a htr126a htr127a htr136a htr137a htr138a htr139a htr1310a htr145b htr146b htr147b htr234a htr235a htr235b htr235c

#print axioms shard_381
end Jsp404.NoSatElevenDBMTerminal
