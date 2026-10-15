import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_20_12_14_H_L_L_I_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h683 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h684 | h684
  · rcases m.htr 0 2 3 (by decide) (by decide) with h685 | h685
    · rcases m.htr 0 2 4 (by decide) (by decide) with h686 | h686
      · rcases m.htr 0 2 5 (by decide) (by decide) with h687 | h687
        · rcases m.htr 0 3 4 (by decide) (by decide) with h688 | h688
          · rcases m.htr 0 4 5 (by decide) (by decide) with h689 | h689
            · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
              · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                · rcases m.htr 1 2 5 (by decide) (by decide) with h692 | h692
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h693 | h693
                    · linarith only [h0, h683, h693, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h688, h693, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h687, h692, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h683, h686, h690, h691, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h685, h690, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h699 | h699
              · rcases m.htr 1 2 4 (by decide) (by decide) with h700 | h700
                · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h702 | h702
                    · linarith only [h683, h702, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h688, h702, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h687, h701, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h683, h686, h699, h700, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h685, h699, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h708 | h708
            · rcases m.htr 1 2 3 (by decide) (by decide) with h709 | h709
              · rcases m.htr 1 2 4 (by decide) (by decide) with h710 | h710
                · rcases m.htr 1 2 5 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
                    · linarith only [h683, h688, h712, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h714 | h714
                      · linarith only [h0, h684, h714, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h684, h708, h714, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h687, h711, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h683, h686, h709, h710, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h685, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
              · rcases m.htr 1 2 4 (by decide) (by decide) with h721 | h721
                · rcases m.htr 1 2 5 (by decide) (by decide) with h722 | h722
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h723 | h723
                    · linarith only [h683, h688, h723, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h725 | h725
                      · linarith only [h684, h708, h725, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                        · linarith only [h683, h688, h720, h727, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h729 | h729
                          · linarith only [h0, h684, h720, h723, h729, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                            · linarith only [h684, h708, h721, h731, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                              · rcases h2bigk with h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, hlam, p734_1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p734_1, u0elo1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p734_1, u0elo1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  rcases p734_3 (m.d 0 2) (by simp) with h740 | h740
                                  · linarith only [h0, h740, hlam]
                                  · rcases p734_3 (m.d 1 2) (by simp) with h742 | h742
                                    · rcases p734_3 (m.d 2 3) (by simp) with h743 | h743
                                      · linarith only [h720, h743, hlam]
                                      · rcases p734_3 (m.d 2 4) (by simp) with h745 | h745
                                        · linarith only [h721, h745, hlam]
                                        · rcases p734_3 (m.d 2 5) (by simp) with h747 | h747
                                          · linarith only [h722, h747, hlam]
                                          · rcases h4bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h708, h723, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1, u0elo4]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h708, h727, h733, hc23, hc34, hlam, hphi, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h688, hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h708, hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h684, hlam, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h0, h684, h727, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p734_1, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h723, hlam, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h725, hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h686, hlam, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h721, hlam, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h727, hlam, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h731, hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              rcases p749_3 (m.d 0 4) (by simp) with h765 | h765
                                              · linarith only [h688, h765, hlam]
                                              · rcases p749_3 (m.d 1 4) (by simp) with h767 | h767
                                                · linarith only [h723, h767, hlam]
                                                · rcases p749_3 (m.d 2 4) (by simp) with h769 | h769
                                                  · linarith only [h727, h769, hlam]
                                                  · rcases p749_3 (m.d 3 4) (by simp) with h771 | h771
                                                    · rcases p749_3 (m.d 4 5) (by simp) with h772 | h772
                                                      · linarith only [h733, h772, hlam]
                                                      · linarith only [h708, h772, hlam]
                                                    · linarith only [h688, h771, hlam]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              rcases p749_3 (m.d 0 4) (by simp) with h776 | h776
                                              · linarith only [h688, h776, hlam]
                                              · linarith only [h684, h776, hlam]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              rcases p749_3 (m.d 0 4) (by simp) with h779 | h779
                                              · linarith only [h688, h779, hlam]
                                              · linarith only [h686, h779, hlam]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h686, h708, h727, hc23, hc34, hlam, hphi, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h683, h688, h720, h733, hc23, hc34, hlam, hphi, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h721, h727, h733, hc23, hc34, hlam, hphi, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h727, h733, hc23, hc34, hlam, hphi, p749_1]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [h733, hlam, p749_0]
                                            · have p749_0 := h749c.1
                                              have p749_1 := h749c.2.1
                                              have p749_2 := h749c.2.2.1
                                              have p749_3 := h749c.2.2.2
                                              linarith only [hlam, p749_0]
                                    · linarith only [h0, h742, hlam]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  rcases p734_3 (m.d 0 2) (by simp) with h791 | h791
                                  · linarith only [h0, h791, hlam]
                                  · linarith only [h685, h791, hlam]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  rcases p734_3 (m.d 0 2) (by simp) with h794 | h794
                                  · linarith only [h0, h794, hlam]
                                  · linarith only [h686, h794, hlam]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  rcases p734_3 (m.d 0 2) (by simp) with h797 | h797
                                  · linarith only [h0, h797, hlam]
                                  · linarith only [h687, h797, hlam]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h685, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h720, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h727, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h729, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h686, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h721, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, h684, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h731, hlam, p734_1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h687, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h722, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h687, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h687, hc24, hlam, hphi, ht0b, ht45, ht5b, p734_1, u0elo1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                              · rcases h2bigk with h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c | h815c
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h0, hlam, p815_1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1, u0elo1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h727, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1, u0elo1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p815_1, u0elo1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  rcases p815_3 (m.d 0 2) (by simp) with h821 | h821
                                  · linarith only [h0, h821, hlam]
                                  · rcases p815_3 (m.d 1 2) (by simp) with h823 | h823
                                    · rcases p815_3 (m.d 2 3) (by simp) with h824 | h824
                                      · linarith only [h720, h824, hlam]
                                      · rcases p815_3 (m.d 2 4) (by simp) with h826 | h826
                                        · linarith only [h721, h826, hlam]
                                        · rcases p815_3 (m.d 2 5) (by simp) with h828 | h828
                                          · linarith only [h722, h828, hlam]
                                          · rcases h4bigk with h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c | h830c
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p830_1, u0elo3]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h0, h684, h727, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p815_1, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h688, hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h708, hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h684, hlam, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h0, h684, h727, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p815_1, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h723, hlam, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h725, hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h686, hlam, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h721, hlam, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h727, hlam, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h731, hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h733, hc04, hc45, hlam, hphi, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h733, hc14, hc45, hlam, hphi, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h727, h733, hc23, hc45, hlam, hphi, ht34, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h733, hlam, p830_0]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              rcases p830_3 (m.d 0 4) (by simp) with h851 | h851
                                              · linarith only [h851, hlam, p830_0]
                                              · rcases p830_3 (m.d 1 4) (by simp) with h853 | h853
                                                · linarith only [h725, h853, hlam]
                                                · rcases p830_3 (m.d 2 4) (by simp) with h855 | h855
                                                  · linarith only [h731, h855, hlam]
                                                  · rcases p830_3 (m.d 3 4) (by simp) with h857 | h857
                                                    · linarith only [h733, h857, hlam]
                                                    · linarith only [h688, h857, hlam]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              rcases p830_3 (m.d 0 4) (by simp) with h860 | h860
                                              · linarith only [h708, h860, hlam]
                                              · linarith only [h684, h860, hlam]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              rcases p830_3 (m.d 0 4) (by simp) with h863 | h863
                                              · linarith only [h708, h863, hlam]
                                              · linarith only [h686, h863, hlam]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [h683, h688, h720, hc23, hc45, hlam, hphi, ht34, p830_1]
                                            · have p830_0 := h830c.1
                                              have p830_1 := h830c.2.1
                                              have p830_2 := h830c.2.2.1
                                              have p830_3 := h830c.2.2.2
                                              linarith only [hlam, p830_0]
                                    · linarith only [h0, h823, hlam]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  rcases p815_3 (m.d 0 2) (by simp) with h870 | h870
                                  · linarith only [h0, h870, hlam]
                                  · linarith only [h685, h870, hlam]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  rcases p815_3 (m.d 0 2) (by simp) with h873 | h873
                                  · linarith only [h0, h873, hlam]
                                  · linarith only [h686, h873, hlam]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  rcases p815_3 (m.d 0 2) (by simp) with h876 | h876
                                  · linarith only [h0, h876, hlam]
                                  · linarith only [h687, h876, hlam]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h685, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h720, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h727, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h729, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h686, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h721, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h684, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1, u0elo0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h731, hlam, p815_1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h687, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h722, hlam, p815_0]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h687, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p815_1, u0elo1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [h687, hc24, hlam, hphi, ht0b, ht45, ht5b, p815_1, u0elo1]
                                · have p815_0 := h815c.1
                                  have p815_1 := h815c.2.1
                                  have p815_2 := h815c.2.2.1
                                  have p815_3 := h815c.2.2.2
                                  linarith only [hlam, p815_0]
                  · linarith only [h687, h722, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h686, h721, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h683, h685, h720, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h897 | h897
          · rcases m.htr 0 4 5 (by decide) (by decide) with h898 | h898
            · linarith only [h0, h684, h687, h898, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h900 | h900
              · rcases m.htr 1 2 4 (by decide) (by decide) with h901 | h901
                · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                    · linarith only [h0, h683, h687, h903, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h683, h687, h897, h903, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h906 | h906
                    · linarith only [h0, h683, h687, h906, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h683, h687, h897, h906, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h686, h687, h901, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h685, h687, h900, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h911 | h911
            · linarith only [h0, h684, h687, h911, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h913 | h913
              · rcases m.htr 1 2 4 (by decide) (by decide) with h914 | h914
                · rcases m.htr 1 2 5 (by decide) (by decide) with h915 | h915
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h916 | h916
                    · linarith only [h0, h683, h687, h897, h916, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h918 | h918
                      · linarith only [h0, h684, h687, h897, h911, h918, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h920 | h920
                        · linarith only [h683, h897, h913, h920, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h922 | h922
                          · linarith only [h0, h683, h687, h913, h922, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h924 | h924
                            · linarith only [h0, h684, h687, h914, h918, h924, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                              · linarith only [h0, h684, h687, h915, h916, h918, h926, hc13, hc34, hlam, hphi]
                              · rcases h2bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, hlam, p928_1]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h687, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u0elo4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h687, hc24, hlam, hphi, ht0b, ht45, ht5b, p928_1, u0elo4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h687, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  rcases p928_3 (m.d 0 2) (by simp) with h934 | h934
                                  · linarith only [h0, h934, hlam]
                                  · rcases p928_3 (m.d 1 2) (by simp) with h936 | h936
                                    · rcases p928_3 (m.d 2 3) (by simp) with h937 | h937
                                      · linarith only [h913, h937, hlam]
                                      · rcases p928_3 (m.d 2 4) (by simp) with h939 | h939
                                        · linarith only [h914, h939, hlam]
                                        · rcases p928_3 (m.d 2 5) (by simp) with h941 | h941
                                          · linarith only [h915, h941, hlam]
                                          · linarith only [h687, h941, hlam]
                                    · linarith only [h0, h936, hlam]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h685, h687, h915, hlam, p928_2]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h686, h687, h915, hlam, p928_2]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, h687, hc01, hc12, hlam, hphi, p928_1]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h685, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h913, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h920, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h922, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h686, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h914, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h684, h914, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u0elo0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h924, hlam, p928_1]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, h684, h915, h918, hc14, hc45, hlam, hphi, p928_1]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h915, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  rcases p928_3 (m.d 0 2) (by simp) with h961 | h961
                                  · linarith only [h687, h961, hlam]
                                  · linarith only [h685, h961, hlam]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  rcases p928_3 (m.d 0 2) (by simp) with h964 | h964
                                  · linarith only [h687, h964, hlam]
                                  · linarith only [h686, h964, hlam]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
                    · linarith only [h683, h897, h968, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h970 | h970
                      · linarith only [h684, h970, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
                        · linarith only [h683, h897, h913, h972, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h974 | h974
                          · linarith only [h685, h687, h974, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h0, h684, h913, h915, h968, h974, hc23, hc35, hlam, hphi]
                · linarith only [h0, h683, h686, h687, h913, h914, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h685, h687, h913, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
      · linarith only [h0, h684, h686, hlam]
    · linarith only [h0, h683, h685, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h981 | h981
    · rcases m.htr 0 2 4 (by decide) (by decide) with h982 | h982
      · rcases m.htr 0 2 5 (by decide) (by decide) with h983 | h983
        · rcases m.htr 0 3 4 (by decide) (by decide) with h984 | h984
          · linarith only [h683, h684, h984, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h986 | h986
            · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
              · rcases m.htr 1 2 4 (by decide) (by decide) with h988 | h988
                · rcases m.htr 1 2 5 (by decide) (by decide) with h989 | h989
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h990 | h990
                    · linarith only [h683, h984, h990, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                        · linarith only [h683, h684, h987, h990, h993, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h995 | h995
                          · linarith only [h683, h987, h995, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h997 | h997
                            · linarith only [h982, h997, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h982, h986, h997, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h684, h982, h986, h992, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h683, h684, h983, h987, h988, h989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h982, h988, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h981, h987, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1006 | h1006
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
                    · linarith only [h1007, h683, h984, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1009 | h1009
                      · linarith only [h1004, h1007, h1009, h683, h684, h986, hc23, hc34, hlam, hphi]
                      · linarith only [h1004, h1009, h683, h684, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1004, h1005, h1006, h683, h684, h983, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1005, h982, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1004, h981, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1015 | h1015
          · linarith only [h1015, h683, h684, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1017 | h1017
            · linarith only [h1017, h982, h983, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1019 | h1019
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1020 | h1020
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1021 | h1021
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
                    · linarith only [h1015, h1022, h683, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1024 | h1024
                      · linarith only [h1017, h1019, h1022, h1024, h683, h684, hc23, hc34, hlam, hphi]
                      · linarith only [h1019, h1024, h683, h684, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1027 | h1027
                    · linarith only [h1027, h683, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1029 | h1029
                      · linarith only [h1017, h1019, h1027, h1029, h683, h684, hc23, hc34, hlam, hphi]
                      · linarith only [h1019, h1029, h683, h684, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1020, h982, h983, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h1019, h981, h983, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1034 | h1034
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1035 | h1035
          · linarith only [h0, h1035, h683, h982, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1037 | h1037
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1038 | h1038
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1039 | h1039
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1040 | h1040
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                    · linarith only [h1035, h1041, h683, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1043 | h1043
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1044 | h1044
                        · linarith only [h0, h1038, h1039, h1041, h1044, h683, h982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1046 | h1046
                          · linarith only [h1038, h1046, h683, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1048 | h1048
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1049 | h1049
                              · rcases h2bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h0, hlam, p1050_1]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h982, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1050_1, u0elo3]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h982, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h982, hc25, hlam, hphi, ht0b, ht5b, p1050_1, u0elo3]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  rcases p1050_3 (m.d 0 2) (by simp) with h1056 | h1056
                                  · linarith only [h0, h1056, hlam]
                                  · rcases p1050_3 (m.d 1 2) (by simp) with h1058 | h1058
                                    · rcases p1050_3 (m.d 2 3) (by simp) with h1059 | h1059
                                      · linarith only [h1038, h1059, hlam]
                                      · rcases p1050_3 (m.d 2 4) (by simp) with h1061 | h1061
                                        · linarith only [h1039, h1061, hlam]
                                        · linarith only [h1061, h982, hlam]
                                    · linarith only [h0, h1058, hlam]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1039, h981, h982, hlam, p1050_2]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h0, h982, hc01, hc12, hlam, hphi, p1050_1]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1034, h1039, h982, hlam, p1050_2]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h981, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1038, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1044, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1046, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h0, h1038, h1039, h1041, h683, hc23, hc34, hlam, hphi, p1050_1]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1039, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  rcases p1050_3 (m.d 0 2) (by simp) with h1076 | h1076
                                  · linarith only [h1076, h982, hlam]
                                  · linarith only [h1076, h981, hlam]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  rcases p1050_3 (m.d 0 2) (by simp) with h1080 | h1080
                                  · linarith only [h1080, h982, hlam]
                                  · linarith only [h1034, h1080, hlam]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1034, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1040, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1034, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1050_1, u0elo1]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [h1048, hlam, p1050_0]
                                · have p1050_0 := h1050c.1
                                  have p1050_1 := h1050c.2.1
                                  have p1050_2 := h1050c.2.2.1
                                  have p1050_3 := h1050c.2.2.2
                                  linarith only [hlam, p1050_0]
                              · linarith only [h1038, h1041, h1049, h683, h684, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h1037, h1048, h982, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1037, h1038, h1039, h1043, h683, h982, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1038, h1039, h1040, h683, h982, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1093 | h1093
                    · linarith only [h1093, h683, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1095 | h1095
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1096 | h1096
                        · linarith only [h0, h1038, h1039, h1093, h1096, h683, hlam]
                        · linarith only [h0, h1038, h1039, h1096, h683, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1037, h1038, h1039, h1095, h683, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1034, h1038, h1092, h683, h982, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h1038, h981, h982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h1034, h1037, h982, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1103 | h1103
          · linarith only [h0, h1103, h683, h982, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1105 | h1105
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1106 | h1106
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1108 | h1108
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1109 | h1109
                    · linarith only [h0, h1034, h1103, h1105, h1109, h683, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1111 | h1111
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1112 | h1112
                        · linarith only [h0, h1034, h1106, h1108, h1109, h1111, h1112, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1114 | h1114
                          · linarith only [h1106, h1114, h683, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1117 | h1117
                              · rcases h2bigk with h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h0, hlam, p1118_1]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1034, h1105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1, u0elo3]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h982, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1034, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  rcases p1118_3 (m.d 0 2) (by simp) with h1124 | h1124
                                  · linarith only [h0, h1124, hlam]
                                  · rcases p1118_3 (m.d 1 2) (by simp) with h1126 | h1126
                                    · rcases p1118_3 (m.d 2 3) (by simp) with h1127 | h1127
                                      · linarith only [h1106, h1127, hlam]
                                      · rcases p1118_3 (m.d 2 4) (by simp) with h1129 | h1129
                                        · linarith only [h1107, h1129, hlam]
                                        · linarith only [h1129, h982, hlam]
                                    · linarith only [h0, h1126, hlam]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1034, h1107, h1116, h981, hlam, p1118_2]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h0, h1034, h1116, hc01, hc12, hlam, hphi, p1118_1]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h0, h1034, h1106, h683, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1118_1]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h981, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1106, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1112, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1114, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h0, h1106, h1107, h683, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1118_1]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1107, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  rcases p1118_3 (m.d 0 2) (by simp) with h1144 | h1144
                                  · linarith only [h1144, h982, hlam]
                                  · linarith only [h1144, h981, hlam]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h0, h1034, h1106, h1107, h683, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1118_1]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h0, h1106, h1114, h683, hc23, hc35, hlam, hphi, p1118_1]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1108, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  rcases p1118_3 (m.d 0 2) (by simp) with h1151 | h1151
                                  · linarith only [h1034, h1151, hlam]
                                  · linarith only [h1151, h981, hlam]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [h1116, hlam, p1118_0]
                                · have p1118_0 := h1118c.1
                                  have p1118_1 := h1118c.2.1
                                  have p1118_2 := h1118c.2.2.1
                                  have p1118_3 := h1118c.2.2.2
                                  linarith only [hlam, p1118_0]
                              · linarith only [h1106, h1109, h1117, h683, h684, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h1105, h1116, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h1105, h1111, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1106, h1107, h1108, h683, h982, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1160 | h1160
                  · linarith only [h0, h1034, h1106, h1107, h1160, h683, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1162 | h1162
                    · linarith only [h1103, h1162, h683, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1164 | h1164
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1165 | h1165
                        · linarith only [h0, h1106, h1160, h1162, h1164, h1165, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1107, h1165, h683, hc13, hc34, hlam, hphi]
                      · linarith only [h1105, h1164, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h0, h1034, h1105, h1106, h981, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1170 | h1170
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1171 | h1171
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1172 | h1172
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1173 | h1173
                    · linarith only [h1173, h683, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1175 | h1175
                      · linarith only [h0, h1105, h1170, h1173, h1175, h683, h982, hc23, hc34, hlam, hphi]
                      · linarith only [h1170, h1175, h683, h684, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1170, h1171, h1172, h683, h982, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1179 | h1179
                  · linarith only [h0, h1034, h1170, h1171, h1179, h683, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
                    · linarith only [h1181, h683, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1183 | h1183
                      · linarith only [h0, h1105, h1170, h1181, h1183, h683, h982, hc23, hc34, hlam, hphi]
                      · linarith only [h1170, h1183, h683, h684, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1105, h1170, h981, h982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
    · linarith only [h0, h683, h981, hlam]

set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_20_12_14_H_L_L_I_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h683 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1189 | h1189
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1190 | h1190
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1191 | h1191
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1192 | h1192
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1193 | h1193
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1194 | h1194
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1195 | h1195
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1196 | h1196
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1197 | h1197
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1198 | h1198
                    · linarith only [h1188, h1198, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1188, h1189, h1193, h1198, h683, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1189, h1192, h1197, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1188, h1191, h1194, h1195, h1196, h683, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h1190, h1194, h1195, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1189, h1194, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1205 | h1205
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1206 | h1206
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1207 | h1207
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1208 | h1208
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1209 | h1209
                    · linarith only [h1188, h1193, h1209, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1211 | h1211
                      · linarith only [h1189, h1211, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1188, h1189, h1208, h1211, h683, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1189, h1192, h1208, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1188, h1191, h1205, h1206, h1207, h683, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h1190, h1205, h1206, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1188, h1189, h1205, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
        · linarith only [h1188, h1192, h683, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1219 | h1219
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1220 | h1220
          · linarith only [h1188, h1189, h1191, h1220, h683, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1222 | h1222
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1223 | h1223
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1224 | h1224
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1225 | h1225
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1226 | h1226
                    · linarith only [h1188, h1189, h1191, h1220, h1226, h683, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1228 | h1228
                      · linarith only [h1189, h1191, h1228, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h1189, h1191, h1219, h1228, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h1219, h1225, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1233 | h1233
                    · linarith only [h1188, h1222, h1224, h1233, h683, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1235 | h1235
                      · linarith only [h1189, h1191, h1235, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h1189, h1191, h1219, h1235, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h1189, h1191, h1219, h1232, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h1188, h1190, h1191, h1222, h1223, h683, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
            · linarith only [h0, h1188, h1189, h1191, h1222, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
        · linarith only [h1188, h1219, h683, hlam]
    · linarith only [h1188, h1189, h1190, h683, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1243 | h1243
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1244 | h1244
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1245 | h1245
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1246 | h1246
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1247 | h1247
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1249 | h1249
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1250 | h1250
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1251 | h1251
                    · linarith only [h1188, h1251, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1246, h1251, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1189, h1245, h1247, h1250, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1188, h1189, h1247, h1248, h1249, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h1188, h1189, h1247, h1248, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1257 | h1257
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1258 | h1258
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1259 | h1259
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1260 | h1260
                    · linarith only [h1188, h1260, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1246, h1260, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1245, h1247, h1259, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1188, h1189, h1244, h1257, h1258, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h0, h1189, h1243, h1257, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1266 | h1266
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1268 | h1268
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                    · linarith only [h1188, h1246, h1270, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1273 | h1273
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1274 | h1274
                          · linarith only [h1188, h1246, h1267, h1274, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1276 | h1276
                            · linarith only [h1188, h1246, h1267, h1272, h1276, hlam]
                            · rcases h2bigk with h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h0, hlam, p1278_1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1189, hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1189, h1272, hc34, hlam, hphi, ht0b, ht45, ht5b, p1278_1, u0elo2]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1189, hc25, hlam, hphi, ht0b, ht5b, p1278_1, u0elo2]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                rcases p1278_3 (m.d 0 2) (by simp) with h1284 | h1284
                                · linarith only [h0, h1284, hlam]
                                · rcases p1278_3 (m.d 1 2) (by simp) with h1286 | h1286
                                  · rcases p1278_3 (m.d 2 3) (by simp) with h1287 | h1287
                                    · linarith only [h1266, h1287, hlam]
                                    · linarith only [h1189, h1287, hlam]
                                  · linarith only [h0, h1286, hlam]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h0, h1189, hc01, hc12, hlam, hphi, p1278_1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h0, h1188, h1189, h1266, h1267, hlam, p1278_2]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1189, h1244, h1266, hlam, p1278_2]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h0, h1188, h1266, h1267, h1272, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1278_1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1266, hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                rcases p1278_3 (m.d 0 2) (by simp) with h1298 | h1298
                                · linarith only [h1189, h1298, hlam]
                                · linarith only [h1243, h1298, hlam]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                rcases p1278_3 (m.d 0 2) (by simp) with h1301 | h1301
                                · linarith only [h1189, h1301, hlam]
                                · linarith only [h1244, h1301, hlam]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1243, hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1267, hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1272, hlam, p1278_1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1274, hlam, p1278_1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1244, hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1268, hlam, p1278_0]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1273, hlam, p1278_1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [h1244, h1272, hc34, hlam, hphi, ht0b, ht45, ht5b, p1278_1, u0elo1]
                              · have p1278_0 := h1278c.1
                                have p1278_1 := h1278c.2.1
                                have p1278_2 := h1278c.2.2.1
                                have p1278_3 := h1278c.2.2.2
                                linarith only [hlam, p1278_0]
                        · linarith only [h1189, h1244, h1273, hlam]
                      · linarith only [h1189, h1245, h1272, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1189, h1245, h1266, h1269, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h1244, h1268, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1189, h1266, h1267, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1319 | h1319
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1320 | h1320
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1321 | h1321
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1322 | h1322
                    · linarith only [h1188, h1246, h1322, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1324 | h1324
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1325 | h1325
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1326 | h1326
                          · linarith only [h1188, h1246, h1319, h1326, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1328 | h1328
                            · linarith only [h1188, h1246, h1319, h1324, h1328, hlam]
                            · rcases h2bigk with h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h0, hlam, p1330_1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1189, hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1189, hc24, hlam, hphi, ht0b, ht45, ht5b, p1330_1, u0elo2]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1189, hc25, hlam, hphi, ht0b, ht5b, p1330_1, u0elo2]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1266, hc02, hc23, hlam, hphi, p1330_1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1266, hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                rcases p1330_3 (m.d 0 2) (by simp) with h1339 | h1339
                                · linarith only [h0, h1339, hlam]
                                · linarith only [h1243, h1339, hlam]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                rcases p1330_3 (m.d 0 2) (by simp) with h1342 | h1342
                                · linarith only [h0, h1342, hlam]
                                · linarith only [h1244, h1342, hlam]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                rcases p1330_3 (m.d 0 2) (by simp) with h1345 | h1345
                                · linarith only [h1345, hlam, p1330_0]
                                · rcases p1330_3 (m.d 1 2) (by simp) with h1347 | h1347
                                  · linarith only [h1266, h1347, hlam]
                                  · linarith only [h0, h1347, hlam]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1330_1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h0, h1188, h1266, h1319, hlam, p1330_2]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                rcases p1330_3 (m.d 0 2) (by simp) with h1353 | h1353
                                · linarith only [h1189, h1353, hlam]
                                · linarith only [h1244, h1353, hlam]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1243, hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1319, hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1324, hlam, p1330_1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1326, hlam, p1330_1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1244, hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1320, hlam, p1330_0]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1325, hlam, p1330_1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [h1244, h1324, hc34, hlam, hphi, ht0b, ht45, ht5b, p1330_1, u0elo1]
                              · have p1330_0 := h1330c.1
                                have p1330_1 := h1330c.2.1
                                have p1330_2 := h1330c.2.2.1
                                have p1330_3 := h1330c.2.2.2
                                linarith only [hlam, p1330_0]
                        · linarith only [h0, h1188, h1266, h1319, h1324, h1325, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1188, h1266, h1319, h1324, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1188, h1245, h1266, h1319, h1321, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h1188, h1189, h1244, h1319, h1320, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h0, h1189, h1243, h1319, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
        · linarith only [h0, h1188, h1189, h1245, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1372 | h1372
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1373 | h1373
          · linarith only [h0, h1188, h1244, h1373, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1375 | h1375
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1376 | h1376
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1377 | h1377
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1378 | h1378
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1379 | h1379
                    · linarith only [h0, h1188, h1189, h1373, h1379, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1381 | h1381
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1382 | h1382
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1383 | h1383
                          · linarith only [h0, h1188, h1244, h1376, h1377, h1379, h1383, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1385 | h1385
                            · linarith only [h0, h1188, h1244, h1376, h1377, h1379, h1381, h1385, hlam]
                            · rcases h2bigk with h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1189, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1244, h1375, h1382, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1244, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 2) (by simp) with h1393 | h1393
                                · linarith only [h0, h1393, hlam]
                                · rcases p1387_3 (m.d 1 2) (by simp) with h1395 | h1395
                                  · rcases p1387_3 (m.d 2 3) (by simp) with h1396 | h1396
                                    · linarith only [h1375, h1396, hlam]
                                    · linarith only [h1189, h1396, hlam]
                                  · linarith only [h0, h1395, hlam]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, h1244, h1382, hc01, hc12, hlam, hphi, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1243, h1244, h1375, h1382, hlam, p1387_2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, h1188, h1244, h1376, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, h1188, h1375, h1376, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1375, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 2) (by simp) with h1407 | h1407
                                · linarith only [h1189, h1407, hlam]
                                · linarith only [h1243, h1407, hlam]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, h1188, h1244, h1375, h1376, h1381, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1243, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1376, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1381, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1383, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, h1188, h1376, h1377, h1379, h1381, hc34, hc45, hlam, hphi, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1377, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1382, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 2) (by simp) with h1419 | h1419
                                · linarith only [h1244, h1419, hlam]
                                · linarith only [h1243, h1419, hlam]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1423 | h1423
                          · linarith only [h1188, h1376, h1379, h1423, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1425 | h1425
                            · linarith only [h0, h1188, h1189, h1376, h1379, h1381, h1382, h1425, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h1188, h1189, h1376, h1381, h1382, h1425, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1188, h1189, h1372, h1376, h1381, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1188, h1189, h1372, h1375, h1376, h1378, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h1188, h1189, h1375, h1376, h1377, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h1188, h1189, h1375, h1376, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1432 | h1432
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1433 | h1433
                · linarith only [h0, h1188, h1244, h1375, h1432, h1433, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1436 | h1436
                    · linarith only [h1188, h1436, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1438 | h1438
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1439 | h1439
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1440 | h1440
                          · linarith only [h0, h1243, h1244, h1433, h1436, h1440, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                          · linarith only [h0, h1188, h1432, h1433, h1438, h1440, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h1188, h1375, h1432, h1438, h1439, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1188, h1375, h1432, h1438, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h1372, h1435, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h1188, h1243, h1432, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
        · linarith only [h0, h1188, h1189, h1372, hlam]
    · linarith only [h0, h1188, h1243, hlam]

end R2N4
