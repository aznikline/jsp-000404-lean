import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_57S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h705 | h705
  · rcases m.htr 0 2 5 (by decide) (by decide) with h706 | h706
    · rcases m.htr 0 3 4 (by decide) (by decide) with h707 | h707
      · rcases m.htr 0 3 5 (by decide) (by decide) with h708 | h708
        · rcases m.htr 0 4 5 (by decide) (by decide) with h709 | h709
          · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
            · linarith only [h3, h710, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h712 | h712
              · rcases m.htr 1 3 5 (by decide) (by decide) with h713 | h713
                · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h716 | h716
                      · linarith only [h3, h705, h714, h716, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h3, h705, h709, h716, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h3, h715, hc02, hlam, hphi, ht23, u3elo4]
                  · linarith only [h3, h705, h714, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h3, h705, h708, h709, h712, h713, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h707, h710, h712, hc12, hlam, hphi, ht23, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
            · linarith only [h3, h723, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
              · rcases m.htr 1 3 5 (by decide) (by decide) with h726 | h726
                · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h728 | h728
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h729 | h729
                      · linarith only [h3, h705, h709, h727, h729, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · rcases h0bigk with h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          rcases p731_3 (m.d 0 1) (by simp) with h733 | h733
                          · rcases p731_3 (m.d 0 2) (by simp) with h734 | h734
                            · linarith only [h0, h734, hlam]
                            · rcases p731_3 (m.d 0 3) (by simp) with h736 | h736
                              · linarith only [h1, h736, hlam]
                              · linarith only [h3, h736, hlam]
                          · linarith only [h0, h733, hlam]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          rcases p731_3 (m.d 0 1) (by simp) with h740 | h740
                          · rcases p731_3 (m.d 0 2) (by simp) with h741 | h741
                            · linarith only [h0, h741, hlam]
                            · rcases p731_3 (m.d 0 3) (by simp) with h743 | h743
                              · linarith only [h1, h743, hlam]
                              · rcases p731_3 (m.d 0 4) (by simp) with h745 | h745
                                · linarith only [h2, h745, hlam]
                                · rcases p731_3 (m.d 0 5) (by simp) with h747 | h747
                                  · linarith only [h3, h706, h747, hc03, hlam, hphi, p731_1, u3elo2]
                                  · rcases h0emin with h749 | h749 | h749 | h749 | h749
                                    · rcases h3bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h723, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p731_1, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h3, hlam, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p731_1, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h729, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p731_1, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h1, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h723, hlam, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p731_1, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h1, h729, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p731_1, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hc03, hlam, hphi, p750_1, u3elo2]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hc13, hlam, hphi, p750_1, u3elo2]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        rcases p750_3 (m.d 0 3) (by simp) with h764 | h764
                                        · linarith only [h3, h764, hlam]
                                        · linarith only [h707, h764, hlam]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        rcases p750_3 (m.d 0 3) (by simp) with h767 | h767
                                        · linarith only [h3, h767, hlam]
                                        · linarith only [h708, h767, hlam]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h707, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h725, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h727, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h729, hlam, p750_1]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h708, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h726, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h728, hlam, p750_0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [h706, h728, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p750_1, u2elo0]
                                      · have p750_0 := h750c.1
                                        have p750_1 := h750c.2.1
                                        have p750_2 := h750c.2.2.1
                                        have p750_3 := h750c.2.2.2
                                        linarith only [hlam, p750_0]
                                    · linarith only [h749, hlam, ht01, ht12, u2elo0]
                                    · linarith only [h749, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h709, h749, hc45, hlam, ht01, ht12, ht23, ht34]
                                    · linarith only [h706, h749, hlam, ht01, ht12, u2elo0]
                          · linarith only [h1, h740, hlam]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          rcases p731_3 (m.d 0 1) (by simp) with h785 | h785
                          · rcases p731_3 (m.d 0 2) (by simp) with h786 | h786
                            · linarith only [h0, h786, hlam]
                            · linarith only [h705, h786, hlam]
                          · linarith only [h2, h785, hlam]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          rcases p731_3 (m.d 0 1) (by simp) with h790 | h790
                          · rcases p731_3 (m.d 0 2) (by simp) with h791 | h791
                            · linarith only [h0, h791, hlam]
                            · linarith only [h706, h791, hlam]
                          · linarith only [h790, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h0, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h3, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p731_1, u3elo2]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p731_1, u3elo2]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h1, hlam, p731_1]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h3, hc02, hlam, hphi, ht23, p731_1, u3elo2]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          rcases p731_3 (m.d 0 1) (by simp) with h803 | h803
                          · rcases p731_3 (m.d 0 2) (by simp) with h804 | h804
                            · linarith only [h3, h804, hlam]
                            · linarith only [h705, h804, hlam]
                          · linarith only [h2, h803, hlam]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          rcases p731_3 (m.d 0 1) (by simp) with h808 | h808
                          · rcases p731_3 (m.d 0 2) (by simp) with h809 | h809
                            · linarith only [h3, h809, hlam]
                            · linarith only [h706, h809, hlam]
                          · linarith only [h0, h706, h808, hlam]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h2, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h705, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h707, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h709, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h1, h3, h706, h726, h729, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p731_1, u3elo2]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h706, hlam, p731_1]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h708, hlam, p731_0]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [h2, h3, h706, h725, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p731_1, u3elo2]
                        · have p731_0 := h731c.1
                          have p731_1 := h731c.2.1
                          have p731_2 := h731c.2.2.1
                          have p731_3 := h731c.2.2.2
                          linarith only [hlam, p731_0]
                    · linarith only [h1, h3, h726, h728, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h3, h705, h727, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h3, h706, h708, h726, hc13, hlam, hphi, u3elo2]
              · linarith only [h3, h706, h707, h709, h723, h725, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h3, h706, h708, hlam]
      · linarith only [h3, h705, h707, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h829 | h829
      · rcases m.htr 0 3 5 (by decide) (by decide) with h830 | h830
        · rcases m.htr 0 4 5 (by decide) (by decide) with h831 | h831
          · linarith only [h705, h706, h831, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h833 | h833
            · linarith only [h0, h3, h833, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h835 | h835
              · rcases m.htr 1 3 5 (by decide) (by decide) with h836 | h836
                · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h839 | h839
                      · linarith only [h705, h706, h831, h837, h838, h839, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · rcases h0bigk with h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          rcases p841_3 (m.d 0 1) (by simp) with h843 | h843
                          · rcases p841_3 (m.d 0 2) (by simp) with h844 | h844
                            · linarith only [h0, h844, hlam]
                            · rcases p841_3 (m.d 0 3) (by simp) with h846 | h846
                              · linarith only [h1, h846, hlam]
                              · linarith only [h3, h846, hlam]
                          · linarith only [h0, h843, hlam]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          rcases p841_3 (m.d 0 1) (by simp) with h850 | h850
                          · rcases p841_3 (m.d 0 2) (by simp) with h851 | h851
                            · linarith only [h0, h851, hlam]
                            · rcases p841_3 (m.d 0 3) (by simp) with h853 | h853
                              · linarith only [h1, h853, hlam]
                              · rcases p841_3 (m.d 0 4) (by simp) with h855 | h855
                                · linarith only [h2, h855, hlam]
                                · rcases p841_3 (m.d 0 5) (by simp) with h857 | h857
                                  · linarith only [h830, h857, hlam, p841_1]
                                  · rcases h0emin with h859 | h859 | h859 | h859 | h859
                                    · rcases h3bigk with h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c | h860c
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p841_1, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h3, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p841_1, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h839, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p841_1, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h1, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h833, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p841_1, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h1, h839, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p841_1, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hc03, hlam, hphi, p860_1, u3elo2]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hc13, hlam, hphi, p860_1, u3elo2]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        rcases p860_3 (m.d 0 3) (by simp) with h874 | h874
                                        · linarith only [h3, h874, hlam]
                                        · linarith only [h829, h874, hlam]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        rcases p860_3 (m.d 0 3) (by simp) with h877 | h877
                                        · linarith only [h3, h877, hlam]
                                        · linarith only [h830, h877, hlam]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h829, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h835, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h837, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h839, hlam, p860_1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h830, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h836, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h838, hlam, p860_0]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [h836, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p860_1, u3elo1]
                                      · have p860_0 := h860c.1
                                        have p860_1 := h860c.2.1
                                        have p860_2 := h860c.2.2.1
                                        have p860_3 := h860c.2.2.2
                                        linarith only [hlam, p860_0]
                                    · linarith only [h706, h859, hlam, ht01, ht12, u2elo4]
                                    · linarith only [h859, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h3, h705, h859, hlam, ht01, ht12, ht23, u3elo2]
                                    · linarith only [h706, h859, hlam, ht01, ht12, u2elo4]
                          · linarith only [h1, h850, hlam]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          rcases p841_3 (m.d 0 1) (by simp) with h895 | h895
                          · rcases p841_3 (m.d 0 2) (by simp) with h896 | h896
                            · linarith only [h0, h896, hlam]
                            · linarith only [h705, h896, hlam]
                          · linarith only [h2, h895, hlam]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          rcases p841_3 (m.d 0 1) (by simp) with h900 | h900
                          · rcases p841_3 (m.d 0 2) (by simp) with h901 | h901
                            · linarith only [h0, h901, hlam]
                            · rcases p841_3 (m.d 0 3) (by simp) with h903 | h903
                              · linarith only [h1, h903, hlam]
                              · linarith only [h830, h903, hlam]
                          · linarith only [h900, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h0, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h3, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h706, h838, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p841_1, u3elo2]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h706, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h1, hlam, p841_1]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p841_1, u3elo0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          rcases p841_3 (m.d 0 1) (by simp) with h915 | h915
                          · rcases p841_3 (m.d 0 2) (by simp) with h916 | h916
                            · linarith only [h3, h916, hlam]
                            · linarith only [h705, h916, hlam]
                          · linarith only [h2, h915, hlam]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h3, h706, hc02, hlam, hphi, ht23, p841_1, u3elo2]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h2, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h705, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h829, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h831, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h0, h831, hc12, hc45, hlam, hphi, ht23, ht34, p841_1]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h705, h706, h837, h838, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p841_1, u3elo2]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [h830, hlam, p841_0]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          rcases p841_3 (m.d 0 1) (by simp) with h929 | h929
                          · rcases p841_3 (m.d 0 2) (by simp) with h930 | h930
                            · linarith only [h706, h930, hlam]
                            · linarith only [h705, h930, hlam]
                          · linarith only [h2, h929, hlam]
                        · have p841_0 := h841c.1
                          have p841_1 := h841c.2.1
                          have p841_2 := h841c.2.2.1
                          have p841_3 := h841c.2.2.2
                          linarith only [hlam, p841_0]
                    · linarith only [h1, h3, h836, h838, hlam]
                  · linarith only [h3, h837, hc02, hlam, hphi, ht23, u3elo3]
                · linarith only [h830, h836, hc13, hlam, hphi, u3elo0]
              · linarith only [h3, h829, h833, h835, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h939 | h939
          · linarith only [h3, h705, h830, h939, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
            · linarith only [h0, h3, h830, h941, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h943 | h943
              · rcases m.htr 1 3 5 (by decide) (by decide) with h944 | h944
                · linarith only [h3, h830, h944, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h947 | h947
                    · linarith only [h830, h947, hc03, hlam, hphi, u3elo2]
                    · linarith only [h3, h705, h946, h947, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h3, h705, h946, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h829, h830, h943, hc13, hlam, hphi, u3elo4]
      · linarith only [h3, h705, h829, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h953 | h953
    · rcases m.htr 0 3 4 (by decide) (by decide) with h954 | h954
      · rcases m.htr 0 3 5 (by decide) (by decide) with h955 | h955
        · rcases m.htr 0 4 5 (by decide) (by decide) with h956 | h956
          · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
            · linarith only [h0, h3, h957, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h959 | h959
              · rcases m.htr 1 3 5 (by decide) (by decide) with h960 | h960
                · rcases m.htr 2 3 4 (by decide) (by decide) with h961 | h961
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h962 | h962
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                      · rcases h0bigk with h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          rcases p964_3 (m.d 0 1) (by simp) with h966 | h966
                          · rcases p964_3 (m.d 0 2) (by simp) with h967 | h967
                            · linarith only [h0, h967, hlam]
                            · rcases p964_3 (m.d 0 3) (by simp) with h969 | h969
                              · linarith only [h1, h969, hlam]
                              · linarith only [h3, h969, hlam]
                          · linarith only [h0, h966, hlam]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h1, h959, h963, hc01, hc45, hlam, hphi, ht0b, ht5b, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          rcases p964_3 (m.d 0 1) (by simp) with h974 | h974
                          · rcases p964_3 (m.d 0 2) (by simp) with h975 | h975
                            · linarith only [h0, h975, hlam]
                            · rcases p964_3 (m.d 0 3) (by simp) with h977 | h977
                              · linarith only [h1, h977, hlam]
                              · linarith only [h954, h977, hlam]
                          · linarith only [h2, h974, hlam]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          rcases p964_3 (m.d 0 1) (by simp) with h981 | h981
                          · rcases p964_3 (m.d 0 2) (by simp) with h982 | h982
                            · linarith only [h0, h982, hlam]
                            · linarith only [h953, h982, hlam]
                          · linarith only [h981, hlam, p964_0]
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
                          linarith only [h3, hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h705, hlam, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h705, h961, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p964_1, u3elo2]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h1, hlam, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p964_1, u3elo0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h3, h705, h953, h962, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p964_1, u3elo2]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          rcases p964_3 (m.d 0 1) (by simp) with h995 | h995
                          · rcases p964_3 (m.d 0 2) (by simp) with h996 | h996
                            · linarith only [h3, h996, hlam]
                            · linarith only [h953, h996, hlam]
                          · linarith only [h0, h953, h995, hlam]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h2, hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h705, h961, hc02, hlam, hphi, ht23, p964_1, u3elo2]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h954, hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          rcases p964_3 (m.d 0 1) (by simp) with h1004 | h1004
                          · rcases p964_3 (m.d 0 2) (by simp) with h1005 | h1005
                            · linarith only [h1005, h705, hlam]
                            · linarith only [h1005, h953, hlam]
                          · linarith only [h1, h1004, h954, h959, h963, hc03, hc45, hlam, hphi, ht0b, ht5b, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h1, h953, h959, h963, hc02, hc45, hlam, hphi, ht0b, ht5b, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h953, hlam, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h955, hlam, p964_0]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [h956, hlam, p964_1]
                        · have p964_0 := h964c.1
                          have p964_1 := h964c.2.1
                          have p964_2 := h964c.2.2.1
                          have p964_3 := h964c.2.2.2
                          linarith only [hlam, p964_0]
                      · rcases h0bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          rcases p1014_3 (m.d 0 1) (by simp) with h1016 | h1016
                          · rcases p1014_3 (m.d 0 2) (by simp) with h1017 | h1017
                            · linarith only [h0, h1017, hlam]
                            · rcases p1014_3 (m.d 0 3) (by simp) with h1019 | h1019
                              · linarith only [h1, h1019, hlam]
                              · linarith only [h1019, h3, hlam]
                          · linarith only [h0, h1016, hlam]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h954, h956, h963, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h956, h963, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          rcases p1014_3 (m.d 0 1) (by simp) with h1025 | h1025
                          · rcases p1014_3 (m.d 0 2) (by simp) with h1026 | h1026
                            · linarith only [h0, h1026, hlam]
                            · linarith only [h1026, h953, hlam]
                          · linarith only [h1025, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h0, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h3, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h705, hlam, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h705, h956, h961, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1, u3elo2]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1, hlam, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p1014_1, u3elo0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h3, h956, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1, u3elo2]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h3, h956, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1, u3elo2]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h2, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h705, h953, h961, h962, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1, u3elo2]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h954, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h705, h956, h961, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1014_1, u3elo2]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1, h960, h963, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h953, hlam, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h955, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h956, hlam, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                    · linarith only [h3, h960, h962, hc03, hlam, hphi, u3elo1]
                  · linarith only [h3, h961, hc02, hlam, hphi, ht23, u3elo3]
                · linarith only [h3, h953, h955, h959, h960, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h3, h954, h957, h959, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h705, h953, h956, hlam]
        · linarith only [h705, h953, h954, h955, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1056 | h1056
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1057 | h1057
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1058 | h1058
            · linarith only [h0, h1058, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1060 | h1060
              · linarith only [h1, h1060, h954, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1062 | h1062
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                  · linarith only [h1063, h3, h954, hc02, hlam, hphi, u2elo2]
                  · linarith only [h1063, h3, h953, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h1056, h1062, hc13, hlam, hphi, u3elo0]
          · linarith only [h1057, h3, h953, h954, hlam]
        · linarith only [h1056, h3, h953, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1069 | h1069
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1070 | h1070
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1072 | h1072
            · linarith only [h0, h1072, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1074 | h1074
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1076 | h1076
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1077 | h1077
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1078 | h1078
                      · rcases h0bigk with h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          rcases p1079_3 (m.d 0 1) (by simp) with h1081 | h1081
                          · rcases p1079_3 (m.d 0 2) (by simp) with h1082 | h1082
                            · linarith only [h0, h1082, hlam]
                            · rcases p1079_3 (m.d 0 3) (by simp) with h1084 | h1084
                              · linarith only [h1, h1084, hlam]
                              · linarith only [h1084, h3, hlam]
                          · linarith only [h0, h1081, hlam]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h1, h1074, h1078, hc01, hc45, hlam, hphi, ht0b, ht5b, p1079_1]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          rcases p1079_3 (m.d 0 1) (by simp) with h1089 | h1089
                          · rcases p1079_3 (m.d 0 2) (by simp) with h1090 | h1090
                            · linarith only [h0, h1090, hlam]
                            · rcases p1079_3 (m.d 0 3) (by simp) with h1092 | h1092
                              · linarith only [h1, h1092, hlam]
                              · linarith only [h1069, h1092, hlam]
                          · linarith only [h1089, h2, hlam]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          rcases p1079_3 (m.d 0 1) (by simp) with h1096 | h1096
                          · rcases p1079_3 (m.d 0 2) (by simp) with h1097 | h1097
                            · linarith only [h0, h1097, hlam]
                            · rcases p1079_3 (m.d 0 3) (by simp) with h1099 | h1099
                              · linarith only [h1, h1099, hlam]
                              · linarith only [h1070, h1099, hlam]
                          · linarith only [h1096, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h0, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h3, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h705, hlam, p1079_1]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h953, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h1, hlam, p1079_1]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p1079_1, u3elo0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h0, h1071, h3, h953, hc12, hlam, hphi, ht23, p1079_1, u3elo2]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h0, h3, h953, hc12, hlam, hphi, ht23, p1079_1, u3elo2]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h2, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h0, h1076, h705, hc12, hlam, hphi, ht23, p1079_1, u3elo2]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h1069, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h0, h1076, h705, h953, hc12, hlam, hphi, ht23, p1079_1, u3elo2]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h1, h1074, h1078, hc05, hc45, hlam, hphi, ht0b, ht5b, p1079_1]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h0, h953, hc12, hlam, hphi, p1079_1, u2elo4]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h1070, hlam, p1079_0]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [h1071, hlam, p1079_1]
                        · have p1079_0 := h1079c.1
                          have p1079_1 := h1079c.2.1
                          have p1079_2 := h1079c.2.2.1
                          have p1079_3 := h1079c.2.2.2
                          linarith only [hlam, p1079_0]
                      · rcases h0bigk with h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          rcases p1123_3 (m.d 0 1) (by simp) with h1125 | h1125
                          · rcases p1123_3 (m.d 0 2) (by simp) with h1126 | h1126
                            · linarith only [h0, h1126, hlam]
                            · rcases p1123_3 (m.d 0 3) (by simp) with h1128 | h1128
                              · linarith only [h1, h1128, hlam]
                              · linarith only [h1128, h3, hlam]
                          · linarith only [h0, h1125, hlam]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1069, h1071, h1078, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1123_1]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1071, h1078, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1123_1]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          rcases p1123_3 (m.d 0 1) (by simp) with h1134 | h1134
                          · rcases p1123_3 (m.d 0 2) (by simp) with h1135 | h1135
                            · linarith only [h0, h1135, hlam]
                            · rcases p1123_3 (m.d 0 3) (by simp) with h1137 | h1137
                              · linarith only [h1, h1137, hlam]
                              · linarith only [h1070, h1137, hlam]
                          · linarith only [h1134, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h3, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h705, hlam, p1123_1]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h953, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1, hlam, p1123_1]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, ht23, p1123_1, u3elo0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1071, h1078, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1123_1, u3elo2]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, h3, h953, hc12, hlam, hphi, ht23, p1123_1, u3elo2]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h2, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, h1076, h705, hc12, hlam, hphi, ht23, p1123_1, u3elo2]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1069, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, h1076, h705, h953, hc12, hlam, hphi, ht23, p1123_1, u3elo2]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, h1077, h953, hc12, hlam, hphi, ht23, p1123_1, u3elo2]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h0, h1077, h953, hc12, hlam, hphi, ht23, p1123_1, u3elo2]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1070, hlam, p1123_0]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [h1071, hlam, p1123_1]
                        · have p1123_0 := h1123c.1
                          have p1123_1 := h1123c.2.1
                          have p1123_2 := h1123c.2.2.1
                          have p1123_3 := h1123c.2.2.2
                          linarith only [hlam, p1123_0]
                    · linarith only [h0, h1077, h3, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h1, h1069, h1071, h1074, h1076, h3, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h1070, h1074, h1075, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · linarith only [h1069, h1072, h1074, h3, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1165 | h1165
            · linarith only [h0, h1165, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1171 | h1171
                      · linarith only [h1071, h1171, h705, hc02, hlam, hphi, ht23, u3elo3]
                      · rcases h0bigk with h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          rcases p1173_3 (m.d 0 1) (by simp) with h1175 | h1175
                          · rcases p1173_3 (m.d 0 2) (by simp) with h1176 | h1176
                            · linarith only [h0, h1176, hlam]
                            · rcases p1173_3 (m.d 0 3) (by simp) with h1178 | h1178
                              · linarith only [h1, h1178, hlam]
                              · linarith only [h1178, h3, hlam]
                          · linarith only [h0, h1175, hlam]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          rcases p1173_3 (m.d 0 1) (by simp) with h1182 | h1182
                          · rcases p1173_3 (m.d 0 2) (by simp) with h1183 | h1183
                            · linarith only [h0, h1183, hlam]
                            · rcases p1173_3 (m.d 0 3) (by simp) with h1185 | h1185
                              · linarith only [h1, h1185, hlam]
                              · rcases p1173_3 (m.d 0 4) (by simp) with h1187 | h1187
                                · linarith only [h1187, h2, hlam]
                                · rcases p1173_3 (m.d 0 5) (by simp) with h1189 | h1189
                                  · linarith only [h1170, h1189, h953, hc03, hlam, hphi, p1173_1, u3elo2]
                                  · rcases h0emin with h1191 | h1191 | h1191 | h1191 | h1191
                                    · rcases h3bigk with h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c | h1192c
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1168, h1171, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1173_1, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h3, hlam, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1173_1, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1171, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1173_1, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1165, hlam, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1173_1, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1, h1171, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1173_1, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hc03, hlam, hphi, p1192_1, u3elo2]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hc13, hlam, hphi, p1192_1, u3elo2]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        rcases p1192_3 (m.d 0 3) (by simp) with h1206 | h1206
                                        · linarith only [h1206, h3, hlam]
                                        · linarith only [h1069, h1206, hlam]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        rcases p1192_3 (m.d 0 3) (by simp) with h1209 | h1209
                                        · linarith only [h1209, h3, hlam]
                                        · linarith only [h1070, h1209, hlam]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1069, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1167, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1169, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1171, hlam, p1192_1]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1070, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1168, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1170, hlam, p1192_0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [h1, h1168, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1192_1, u3elo0]
                                      · have p1192_0 := h1192c.1
                                        have p1192_1 := h1192c.2.1
                                        have p1192_2 := h1192c.2.2.1
                                        have p1192_3 := h1192c.2.2.2
                                        linarith only [hlam, p1192_0]
                                    · linarith only [h1191, h705, hlam, ht01, ht12, u2elo3]
                                    · linarith only [h1191, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h1071, h1191, hc45, hlam, ht01, ht12, ht23, ht34]
                                    · linarith only [h1170, h1191, h953, hlam, ht01, ht12, ht23, u3elo2]
                          · linarith only [h1, h1182, hlam]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          rcases p1173_3 (m.d 0 1) (by simp) with h1227 | h1227
                          · rcases p1173_3 (m.d 0 2) (by simp) with h1228 | h1228
                            · linarith only [h0, h1228, hlam]
                            · rcases p1173_3 (m.d 0 3) (by simp) with h1230 | h1230
                              · linarith only [h1, h1230, hlam]
                              · linarith only [h1069, h1230, hlam]
                          · linarith only [h1227, h2, hlam]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          rcases p1173_3 (m.d 0 1) (by simp) with h1234 | h1234
                          · rcases p1173_3 (m.d 0 2) (by simp) with h1235 | h1235
                            · linarith only [h0, h1235, hlam]
                            · rcases p1173_3 (m.d 0 3) (by simp) with h1237 | h1237
                              · linarith only [h1, h1237, hlam]
                              · linarith only [h1070, h1237, hlam]
                          · linarith only [h1234, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h0, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h3, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h705, hlam, p1173_1]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h953, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h1, hlam, p1173_1]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p1173_1, u3elo0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h0, h3, h705, hc12, hlam, hphi, ht23, p1173_1, u3elo2]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h0, h3, h953, hc12, hlam, hphi, ht23, p1173_1, u3elo2]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h2, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h0, h1169, h705, hc12, hlam, hphi, ht23, p1173_1, u3elo2]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h1069, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h1071, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h1170, h953, hc01, hlam, hphi, ht12, ht23, p1173_1, u3elo2]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h0, h1170, h953, hc12, hlam, hphi, ht23, p1173_1, u3elo2]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h1070, hlam, p1173_0]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [h0, h1170, h705, h953, hc12, hlam, hphi, ht23, p1173_1, u3elo2]
                        · have p1173_0 := h1173c.1
                          have p1173_1 := h1173c.2.1
                          have p1173_2 := h1173c.2.2.1
                          have p1173_3 := h1173c.2.2.2
                          linarith only [hlam, p1173_0]
                    · linarith only [h1, h1168, h1170, h3, hlam]
                  · linarith only [h0, h1169, h3, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1070, h1168, h3, hc13, hlam, hphi, u3elo2]
              · linarith only [h1069, h1165, h1167, h3, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1265 | h1265
          · linarith only [h1069, h1070, h1265, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1267 | h1267
            · linarith only [h0, h1267, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1270 | h1270
                · linarith only [h1069, h1070, h1270, h705, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1273 | h1273
                    · linarith only [h1, h1070, h1269, h1273, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h0, h1273, h3, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h0, h1, h1269, h1272, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1069, h1070, h1269, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1278 | h1278
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1279 | h1279
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1280 | h1280
            · linarith only [h0, h1280, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1282 | h1282
              · linarith only [h1069, h1278, h1282, h953, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1284 | h1284
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1285 | h1285
                  · linarith only [h1, h1069, h1284, h1285, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h1285, h3, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1069, h1278, h1284, hc13, hlam, hphi, u3elo3]
          · linarith only [h1069, h1278, h1279, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1290 | h1290
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
            · linarith only [h0, h1291, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1293 | h1293
              · linarith only [h1069, h1293, h3, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1295 | h1295
                · linarith only [h1, h1278, h1295, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h0, h1069, h1297, h3, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h0, h1297, h3, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1300 | h1300
            · linarith only [h0, h1300, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
              · linarith only [h1, h1069, h1302, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1304 | h1304
                · linarith only [h1, h1278, h1304, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1306 | h1306
                  · linarith only [h1069, h1306, hc03, hlam, hphi, u3elo2]
                  · linarith only [h0, h1306, h3, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3

set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1309 | h1309
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1310 | h1310
    · linarith only [h0, h1310, h2, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1312 | h1312
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1313 | h1313
        · linarith only [h1, h1313, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1315 | h1315
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1316 | h1316
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1317 | h1317
              · linarith only [h0, h1313, h1317, h2, hc23, hlam, hphi, u3elo3]
              · linarith only [h1309, h1310, h1317, hc12, hlam, hphi, u2elo3]
            · linarith only [h0, h1310, h1312, h1316, h2, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1321 | h1321
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1322 | h1322
              · linarith only [h0, h1313, h1322, h2, hc23, hlam, hphi, u3elo3]
              · linarith only [h1309, h1310, h1322, hc12, hlam, hphi, u2elo3]
            · linarith only [h0, h1310, h1312, h1321, h2, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1326 | h1326
        · linarith only [h1, h1326, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1328 | h1328
          · linarith only [h1309, h1312, h1326, h1328, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1330 | h1330
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
              · linarith only [h0, h1326, h1331, h2, hc23, hlam, hphi, u3elo3]
              · linarith only [h1309, h1312, h1331, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1334 | h1334
              · linarith only [h0, h1328, h1330, h1334, h2, hc23, hlam, hphi, u3elo4]
              · linarith only [h1309, h1312, h1334, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1337 | h1337
    · linarith only [h0, h1337, h2, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1339 | h1339
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1340 | h1340
        · linarith only [h1, h1340, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1342 | h1342
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1343 | h1343
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1344 | h1344
              · linarith only [h0, h1309, h1340, h1344, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1346 | h1346
                · linarith only [h1, h1340, h1346, h2, hlam]
                · linarith only [h1, h1344, h1346, h2, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h0, h1309, h1339, h1340, h1343, h2, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h1309, h1339, h1342, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1351 | h1351
        · linarith only [h1, h1351, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1353 | h1353
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1354 | h1354
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1355 | h1355
              · linarith only [h0, h1339, h1351, h1353, h1355, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1357 | h1357
                · linarith only [h1, h1339, h1351, h1353, h1357, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1357, h2, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h1, h1353, h1354, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1361 | h1361
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1362 | h1362
              · linarith only [h0, h1309, h1362, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1364 | h1364
                · linarith only [h1, h1351, h1364, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1364, h2, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1367 | h1367
              · linarith only [h0, h1353, h1361, h1367, h2, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1369 | h1369
                · linarith only [h1, h1309, h1351, h1353, h1361, h1369, h2, hc02, hlam, hphi, ht23, u3elo4]
                · linarith only [h0, h1369, h2, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2

set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0_x0 m hb0 hb2 hb3 h0 h1
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0_x1 m hb0 hb2 hb3 h0 h1

end R2N4
