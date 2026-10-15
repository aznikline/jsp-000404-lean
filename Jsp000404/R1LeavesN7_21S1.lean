import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h672 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h673 | h673
  · rcases m.htr 0 3 5 (by decide) (by decide) with h674 | h674
    · rcases m.htr 0 4 5 (by decide) (by decide) with h675 | h675
      · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
        · linarith only [h0, h2, h676, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h678 | h678
          · rcases m.htr 1 2 5 (by decide) (by decide) with h679 | h679
            · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
              · rcases m.htr 2 3 4 (by decide) (by decide) with h681 | h681
                · rcases m.htr 2 3 5 (by decide) (by decide) with h682 | h682
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h683 | h683
                    · linarith only [h0, h678, h683, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h678, h680, h683, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h2, h674, h682, hlam]
                · linarith only [h2, h672, h681, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h688 | h688
                · rcases m.htr 2 3 5 (by decide) (by decide) with h689 | h689
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h690 | h690
                    · linarith only [h678, h680, h690, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h692 | h692
                      · linarith only [h678, h680, h688, h692, hlam]
                      · rcases h2bigk with h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p694_1]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h2, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          rcases p694_3 (m.d 0 2) (by simp) with h698 | h698
                          · rcases p694_3 (m.d 1 2) (by simp) with h699 | h699
                            · linarith only [h0, h699, hlam]
                            · linarith only [h678, h699, hlam]
                          · linarith only [h698, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          rcases p694_3 (m.d 0 2) (by simp) with h703 | h703
                          · rcases p694_3 (m.d 1 2) (by simp) with h704 | h704
                            · linarith only [h0, h704, hlam]
                            · linarith only [h679, h704, hlam]
                          · linarith only [h703, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h0, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h676, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h0, h688, hc34, hlam, hphi, ht0b, ht45, ht5b, p694_1, u0elo0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h0, h688, h690, hc34, hlam, hphi, ht0b, ht45, ht5b, p694_1, u0elo0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h672, h675, h678, h680, h688, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p694_1]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          rcases p694_3 (m.d 0 2) (by simp) with h714 | h714
                          · linarith only [h2, h714, hlam]
                          · linarith only [h0, h714, hlam]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h2, h672, h675, h678, h680, hlam, p694_2]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          rcases p694_3 (m.d 0 2) (by simp) with h719 | h719
                          · linarith only [h2, h719, hlam]
                          · linarith only [h673, h719, hlam]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h672, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h678, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h688, hlam, p694_1]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h690, hlam, p694_1]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h673, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h679, hlam, p694_0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h689, hlam, p694_1]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [h0, h679, h688, hc34, hlam, hphi, ht0b, ht45, ht5b, p694_1, u0elo0]
                        · have p694_0 := h694c.1
                          have p694_1 := h694c.2.1
                          have p694_2 := h694c.2.2.1
                          have p694_3 := h694c.2.2.2
                          linarith only [hlam, p694_0]
                  · linarith only [h2, h672, h674, h675, h678, h680, h688, h689, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h2, h672, h675, h680, h688, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h2, h673, h679, hc12, hc23, hlam, hphi]
          · linarith only [h2, h672, h678, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h736 | h736
        · linarith only [h0, h2, h736, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
          · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
            · rcases m.htr 1 4 5 (by decide) (by decide) with h740 | h740
              · linarith only [h0, h672, h675, h738, h740, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h742 | h742
                · rcases m.htr 2 3 5 (by decide) (by decide) with h743 | h743
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h744 | h744
                    · linarith only [h672, h675, h744, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                      · linarith only [h672, h675, h742, h746, hlam]
                      · rcases h2bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p748_1]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h2, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          rcases p748_3 (m.d 0 2) (by simp) with h752 | h752
                          · rcases p748_3 (m.d 1 2) (by simp) with h753 | h753
                            · linarith only [h0, h753, hlam]
                            · linarith only [h738, h753, hlam]
                          · linarith only [h752, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          rcases p748_3 (m.d 0 2) (by simp) with h757 | h757
                          · rcases p748_3 (m.d 1 2) (by simp) with h758 | h758
                            · linarith only [h0, h758, hlam]
                            · linarith only [h739, h758, hlam]
                          · linarith only [h757, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h0, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h736, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h0, h742, hc34, hlam, hphi, ht0b, ht45, ht5b, p748_1, u0elo0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p748_1, u0elo0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          rcases p748_3 (m.d 0 2) (by simp) with h767 | h767
                          · linarith only [h767, hlam, p748_0]
                          · rcases p748_3 (m.d 1 2) (by simp) with h769 | h769
                            · linarith only [h736, h769, hlam]
                            · rcases p748_3 (m.d 2 3) (by simp) with h771 | h771
                              · rcases p748_3 (m.d 2 4) (by simp) with h772 | h772
                                · linarith only [h742, h772, hlam]
                                · rcases p748_3 (m.d 2 5) (by simp) with h774 | h774
                                  · linarith only [h743, h774, hlam]
                                  · rcases h5bigk with h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h738, h740, h742, hc34, hlam, hphi, ht0b, ht45, ht5b, p776_1, u0elo4]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h673, h742, h744, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p748_1, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h673, h746, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p748_1, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h675, hlam, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h1, hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h1, h742, h744, hc34, hlam, hphi, ht0b, ht45, ht5b, p776_1, u0elo0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h1, h746, hc34, hlam, hphi, ht0b, ht45, ht5b, p776_1, u0elo4]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h740, hlam, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h673, hlam, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h739, hlam, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h673, h746, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p748_1, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h744, hlam, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h674, hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h674, hc15, hlam, hphi, ht0b, ht5b, p776_1, u0elo2]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h743, hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [hlam, p776_0]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h746, hlam, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h672, h675, h742, hc34, hc45, hlam, hphi, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h738, h740, h742, hc34, hc45, hlam, hphi, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h742, h744, hc34, hc45, hlam, hphi, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [h746, hc34, hc45, hlam, hphi, p776_1]
                                    · have p776_0 := h776c.1
                                      have p776_1 := h776c.2.1
                                      have p776_2 := h776c.2.2.1
                                      have p776_3 := h776c.2.2.2
                                      linarith only [hlam, p776_0]
                              · linarith only [h771, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          rcases p748_3 (m.d 0 2) (by simp) with h803 | h803
                          · linarith only [h2, h803, hlam]
                          · linarith only [h0, h803, hlam]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          rcases p748_3 (m.d 0 2) (by simp) with h807 | h807
                          · linarith only [h2, h807, hlam]
                          · linarith only [h672, h807, hlam]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          rcases p748_3 (m.d 0 2) (by simp) with h810 | h810
                          · linarith only [h2, h810, hlam]
                          · linarith only [h673, h810, hlam]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h672, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h738, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h742, hlam, p748_1]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h744, hlam, p748_1]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h673, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h739, hlam, p748_0]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h743, hlam, p748_1]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [h0, h739, h742, hc34, hlam, hphi, ht0b, ht45, ht5b, p748_1, u0elo1]
                        · have p748_0 := h748c.1
                          have p748_1 := h748c.2.1
                          have p748_2 := h748c.2.2.1
                          have p748_3 := h748c.2.2.2
                          linarith only [hlam, p748_0]
                  · linarith only [h2, h674, h743, hlam]
                · linarith only [h2, h672, h742, hlam]
            · linarith only [h673, h738, h739, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · linarith only [h2, h672, h738, hc12, hc23, hlam, hphi]
    · linarith only [h2, h673, h674, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h828 | h828
    · rcases m.htr 0 4 5 (by decide) (by decide) with h829 | h829
      · linarith only [h672, h673, h829, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
        · linarith only [h0, h2, h831, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h833 | h833
          · rcases m.htr 1 2 5 (by decide) (by decide) with h834 | h834
            · linarith only [h0, h673, h834, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h836 | h836
              · linarith only [h0, h829, h833, h836, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h838 | h838
                · rcases m.htr 2 3 5 (by decide) (by decide) with h839 | h839
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h840 | h840
                    · linarith only [h672, h673, h829, h840, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                      · linarith only [h673, h838, h840, h842, hc02, hc23, hlam, hphi]
                      · rcases h2bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h833, h838, hc34, hlam, hphi, ht0b, ht45, ht5b, p844_1, u0elo1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h2, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h673, h838, h840, hc34, hc45, hlam, hphi, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h673, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h0, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h831, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h0, h838, hc34, hlam, hphi, ht0b, ht45, ht5b, p844_1, u0elo0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h834, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          rcases p844_3 (m.d 0 2) (by simp) with h855 | h855
                          · linarith only [h855, hlam, p844_0]
                          · rcases p844_3 (m.d 1 2) (by simp) with h857 | h857
                            · linarith only [h831, h857, hlam]
                            · rcases p844_3 (m.d 2 3) (by simp) with h859 | h859
                              · rcases p844_3 (m.d 2 4) (by simp) with h860 | h860
                                · linarith only [h838, h860, hlam]
                                · rcases p844_3 (m.d 2 5) (by simp) with h862 | h862
                                  · linarith only [h839, h862, hlam]
                                  · linarith only [h673, h862, hlam]
                              · linarith only [h859, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          rcases p844_3 (m.d 0 2) (by simp) with h866 | h866
                          · linarith only [h2, h866, hlam]
                          · linarith only [h0, h866, hlam]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          rcases p844_3 (m.d 0 2) (by simp) with h870 | h870
                          · linarith only [h2, h870, hlam]
                          · linarith only [h672, h870, hlam]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h673, hc02, hc23, hlam, hphi, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h672, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h833, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h838, hlam, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h840, hlam, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h0, h833, h838, h840, hc34, hc45, hlam, hphi, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h833, h838, h840, hc34, hc45, hlam, hphi, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h839, hlam, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          rcases p844_3 (m.d 0 2) (by simp) with h882 | h882
                          · linarith only [h673, h882, hlam]
                          · linarith only [h672, h882, hlam]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                  · linarith only [h0, h2, h828, h833, h838, h839, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h0, h2, h828, h833, h838, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
          · linarith only [h2, h672, h833, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
      · linarith only [h672, h673, h889, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h891 | h891
        · linarith only [h0, h2, h891, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h893 | h893
          · rcases m.htr 1 2 5 (by decide) (by decide) with h894 | h894
            · linarith only [h0, h2, h673, h828, h894, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h896 | h896
              · linarith only [h0, h889, h893, h896, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h898 | h898
                · rcases m.htr 2 3 5 (by decide) (by decide) with h899 | h899
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h900 | h900
                    · linarith only [h2, h672, h828, h889, h900, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
                      · linarith only [h0, h2, h828, h893, h898, h899, h900, h902, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h2bigk with h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h893, h898, hc34, hlam, hphi, ht0b, ht45, ht5b, p904_1, u0elo1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h2, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h2, h828, h898, h899, h900, hc34, hc45, hlam, hphi, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h673, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h0, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h891, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h0, h898, hc34, hlam, hphi, ht0b, ht45, ht5b, p904_1, u0elo0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h894, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          rcases p904_3 (m.d 0 2) (by simp) with h915 | h915
                          · linarith only [h915, hlam, p904_0]
                          · rcases p904_3 (m.d 1 2) (by simp) with h917 | h917
                            · linarith only [h891, h917, hlam]
                            · rcases p904_3 (m.d 2 3) (by simp) with h919 | h919
                              · rcases p904_3 (m.d 2 4) (by simp) with h920 | h920
                                · linarith only [h898, h920, hlam]
                                · rcases p904_3 (m.d 2 5) (by simp) with h922 | h922
                                  · linarith only [h899, h922, hlam]
                                  · linarith only [h673, h922, hlam]
                              · linarith only [h919, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          rcases p904_3 (m.d 0 2) (by simp) with h926 | h926
                          · linarith only [h2, h926, hlam]
                          · linarith only [h0, h926, hlam]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h2, h672, h828, h899, hlam, p904_2]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h673, hc02, hc23, hlam, hphi, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h672, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h893, hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h898, hlam, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [hlam, p904_0]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h900, hlam, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h0, h893, h898, h900, hc34, hc45, hlam, hphi, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h893, h898, h900, hc34, hc45, hlam, hphi, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [h899, hlam, p904_1]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          rcases p904_3 (m.d 0 2) (by simp) with h940 | h940
                          · linarith only [h673, h940, hlam]
                          · linarith only [h672, h940, hlam]
                        · have p904_0 := h904c.1
                          have p904_1 := h904c.2.1
                          have p904_2 := h904c.2.2.1
                          have p904_3 := h904c.2.2.2
                          linarith only [hlam, p904_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h944 | h944
                    · linarith only [h0, h2, h893, h899, h944, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h946 | h946
                      · linarith only [h2, h672, h898, h899, h944, h946, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h2, h893, h898, h899, h946, hc34, hc45, hlam, hphi]
                · linarith only [h0, h2, h893, h898, hlam]
          · linarith only [h2, h672, h893, hc12, hc23, hlam, hphi]

set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h672 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h951 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h952 | h952
  · rcases m.htr 0 4 5 (by decide) (by decide) with h953 | h953
    · rcases m.htr 1 2 3 (by decide) (by decide) with h954 | h954
      · linarith only [h0, h2, h954, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
        · linarith only [h0, h672, h951, h956, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h958 | h958
          · rcases m.htr 1 4 5 (by decide) (by decide) with h959 | h959
            · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
              · rcases m.htr 2 3 5 (by decide) (by decide) with h961 | h961
                · rcases m.htr 2 4 5 (by decide) (by decide) with h962 | h962
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                    · rcases h2bigk with h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h958, h961, h963, hc45, hlam, hphi, ht0b, ht5b, p964_1, u0elo1]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h2, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h672, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h969 | h969
                        · rcases p964_3 (m.d 1 2) (by simp) with h970 | h970
                          · linarith only [h0, h970, hlam]
                          · linarith only [h958, h970, hlam]
                        · linarith only [h969, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h0, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h954, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h956, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h0, h961, h963, hc45, hlam, hphi, ht0b, ht5b, p964_1, u0elo0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h979 | h979
                        · linarith only [h979, hlam, p964_0]
                        · rcases p964_3 (m.d 1 2) (by simp) with h981 | h981
                          · linarith only [h954, h981, hlam]
                          · rcases p964_3 (m.d 2 3) (by simp) with h983 | h983
                            · rcases p964_3 (m.d 2 4) (by simp) with h984 | h984
                              · linarith only [h960, h984, hlam]
                              · linarith only [h672, h984, hlam]
                            · linarith only [h983, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h988 | h988
                        · linarith only [h2, h988, hlam]
                        · linarith only [h0, h988, hlam]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h672, hc02, hc23, hlam, hphi, p964_1]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h993 | h993
                        · linarith only [h2, h993, hlam]
                        · linarith only [h951, h993, hlam]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h996 | h996
                        · linarith only [h996, hlam, p964_0]
                        · rcases p964_3 (m.d 1 2) (by simp) with h998 | h998
                          · linarith only [h956, h998, hlam]
                          · rcases p964_3 (m.d 2 3) (by simp) with h1000 | h1000
                            · rcases p964_3 (m.d 2 4) (by simp) with h1001 | h1001
                              · rcases p964_3 (m.d 2 5) (by simp) with h1002 | h1002
                                · linarith only [h1002, h962, hlam]
                                · rcases h5bigk with h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h951, hc15, hlam, hphi, ht0b, ht5b, p1004_1, u0elo1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h951, h960, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h951, h960, h963, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h951, h960, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h1, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h1, h961, h963, hc45, hlam, hphi, ht0b, ht5b, p1004_1, u0elo0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h1, h951, h960, h963, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h1, h951, h960, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h951, hlam, p1004_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h958, hlam, p1004_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h951, h960, h963, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h0, h958, h960, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h952, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h952, hc15, hlam, hphi, ht0b, ht5b, p1004_1, u0elo2]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h961, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h0, h958, h960, h961, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1004_1, p964_1]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h953, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h959, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h962, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [h963, hlam, p1004_0]
                                  · have p1004_0 := h1004c.1
                                    have p1004_1 := h1004c.2.1
                                    have p1004_2 := h1004c.2.2.1
                                    have p1004_3 := h1004c.2.2.2
                                    linarith only [hlam, p1004_0]
                              · linarith only [h1001, hlam, p964_0]
                            · linarith only [h1000, h2, hlam]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h1032 | h1032
                        · linarith only [h1032, h672, hlam]
                        · linarith only [h0, h1032, hlam]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h960, hlam, p964_1]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        rcases p964_3 (m.d 0 2) (by simp) with h1037 | h1037
                        · linarith only [h1037, h672, hlam]
                        · linarith only [h1037, h951, hlam]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h951, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h958, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h961, hlam, p964_1]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [h962, hlam, p964_0]
                      · have p964_0 := h964c.1
                        have p964_1 := h964c.2.1
                        have p964_2 := h964c.2.2.1
                        have p964_3 := h964c.2.2.2
                        linarith only [hlam, p964_0]
                    · linarith only [h0, h958, h962, h963, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h672, h951, h959, h962, hlam]
                · linarith only [h2, h952, h961, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1048 | h1048
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1049 | h1049
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1050 | h1050
                    · rcases h2bigk with h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h2, hc12, hc23, hlam, hphi, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h2, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h672, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h1048, h1050, h2, h960, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h954, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h956, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, h1048, h1050, hc45, hlam, hphi, ht0b, ht5b, p1051_1, u0elo0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h960, hc02, hc34, hlam, hphi, ht23, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h960, hc12, hc34, hlam, hphi, ht23, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h960, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1066 | h1066
                        · linarith only [h1066, h2, hlam]
                        · linarith only [h1066, h951, hlam]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1069 | h1069
                        · linarith only [h1069, hlam, p1051_0]
                        · rcases p1051_3 (m.d 1 2) (by simp) with h1071 | h1071
                          · linarith only [h1071, h956, hlam]
                          · rcases p1051_3 (m.d 2 3) (by simp) with h1073 | h1073
                            · linarith only [h1073, h960, hlam]
                            · linarith only [h1073, h2, hlam]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1076 | h1076
                        · linarith only [h1076, h672, hlam]
                        · linarith only [h0, h1076, hlam]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h2, h960, hc02, hc34, hlam, hphi, ht23, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1081 | h1081
                        · linarith only [h1081, h672, hlam]
                        · linarith only [h1081, h951, hlam]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h951, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h958, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h1048, hlam, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h1049, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                    · linarith only [h1050, h2, h960, hc02, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h1049, h672, h958, h959, hlam]
                · linarith only [h1048, h2, h952, hlam]
            · linarith only [h953, h956, h958, h959, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
          · linarith only [h2, h951, h958, hc12, hc23, hlam, hphi]
    · linarith only [h672, h951, h953, hlam]
  · linarith only [h2, h951, h952, hlam]

end R2N4
