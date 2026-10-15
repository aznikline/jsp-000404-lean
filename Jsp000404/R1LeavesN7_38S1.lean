import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h705 | h705
  · rcases m.htr 0 2 5 (by decide) (by decide) with h706 | h706
    · rcases m.htr 0 3 4 (by decide) (by decide) with h707 | h707
      · rcases m.htr 0 3 5 (by decide) (by decide) with h708 | h708
        · rcases m.htr 0 4 5 (by decide) (by decide) with h709 | h709
          · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
            · linarith only [h4, h705, h709, h710, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h712 | h712
              · rcases m.htr 1 2 5 (by decide) (by decide) with h713 | h713
                · rcases m.htr 1 3 4 (by decide) (by decide) with h714 | h714
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h715 | h715
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h716 | h716
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h717 | h717
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h718 | h718
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
                            · linarith only [h0, h4, h712, h719, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h721 | h721
                              · linarith only [h717, h719, h721, hlam]
                              · rcases h2bigk with h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p723_1]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h4, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  rcases p723_3 (m.d 0 2) (by simp) with h727 | h727
                                  · rcases p723_3 (m.d 1 2) (by simp) with h728 | h728
                                    · linarith only [h0, h728, hlam]
                                    · linarith only [h712, h728, hlam]
                                  · linarith only [h727, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h4, h718, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p723_1, u5ehi8]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h0, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h710, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  rcases p723_3 (m.d 0 2) (by simp) with h736 | h736
                                  · rcases p723_3 (m.d 1 2) (by simp) with h737 | h737
                                    · rcases p723_3 (m.d 2 3) (by simp) with h738 | h738
                                      · rcases p723_3 (m.d 2 4) (by simp) with h739 | h739
                                        · linarith only [h739, hlam, p723_0]
                                        · rcases p723_3 (m.d 2 5) (by simp) with h741 | h741
                                          · linarith only [h713, h741, hlam]
                                          · linarith only [h719, h741, hlam]
                                      · linarith only [h717, h738, hlam]
                                    · linarith only [h737, hlam, p723_0]
                                  · linarith only [h705, h736, hlam]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h0, h718, hc01, hlam, hphi, ht0b, ht5b, p723_1, u5ehi8]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h2, h705, h716, h717, h719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p723_1]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h712, h716, h717, h719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p723_1]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h2, h4, h705, h716, h719, hlam, p723_2]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  rcases p723_3 (m.d 0 2) (by simp) with h752 | h752
                                  · linarith only [h4, h752, hlam]
                                  · linarith only [h706, h752, hlam]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h705, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h712, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h717, hlam, p723_1]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h719, hlam, p723_1]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h706, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h713, hlam, p723_0]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h718, hlam, p723_1]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [h717, hc34, hlam, hphi, ht45, p723_1, u5elo2]
                                · have p723_0 := h723c.1
                                  have p723_1 := h723c.2.1
                                  have p723_2 := h723c.2.2.1
                                  have p723_3 := h723c.2.2.2
                                  linarith only [hlam, p723_0]
                          · linarith only [h2, h4, h705, h716, h718, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                        · linarith only [h0, h4, h713, h717, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h767 | h767
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h768 | h768
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h769 | h769
                            · linarith only [h712, h716, h769, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h771 | h771
                              · linarith only [h712, h716, h767, h771, hlam]
                              · rcases h2bigk with h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h713, h768, hc02, hlam, hphi, ht0b, ht5b, p773_1, u5ehi8]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h4, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  rcases p773_3 (m.d 0 2) (by simp) with h777 | h777
                                  · rcases p773_3 (m.d 1 2) (by simp) with h778 | h778
                                    · linarith only [h0, h778, hlam]
                                    · linarith only [h712, h778, hlam]
                                  · linarith only [h777, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h4, h768, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p773_1, u5ehi8]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h0, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h710, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  rcases p773_3 (m.d 0 2) (by simp) with h786 | h786
                                  · rcases p773_3 (m.d 1 2) (by simp) with h787 | h787
                                    · rcases p773_3 (m.d 2 3) (by simp) with h788 | h788
                                      · rcases p773_3 (m.d 2 4) (by simp) with h789 | h789
                                        · linarith only [h789, hlam, p773_0]
                                        · rcases p773_3 (m.d 2 5) (by simp) with h791 | h791
                                          · linarith only [h713, h791, hlam]
                                          · linarith only [h769, h791, hlam]
                                      · linarith only [h767, h788, hlam]
                                    · linarith only [h787, hlam, p773_0]
                                  · linarith only [h705, h786, hlam]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h0, h768, hc01, hlam, hphi, ht0b, ht5b, p773_1, u5ehi8]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h705, h709, h712, h716, h767, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p773_1]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h713, h768, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p773_1, u5ehi8]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h4, h705, h709, h712, h716, hlam, p773_2]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  rcases p773_3 (m.d 0 2) (by simp) with h802 | h802
                                  · linarith only [h4, h802, hlam]
                                  · linarith only [h706, h802, hlam]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h705, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h712, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h767, hlam, p773_1]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h769, hlam, p773_1]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h706, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h713, hlam, p773_0]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h768, hlam, p773_1]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [h767, hc34, hlam, hphi, ht45, p773_1, u5elo2]
                                · have p773_0 := h773c.1
                                  have p773_1 := h773c.2.1
                                  have p773_2 := h773c.2.2.1
                                  have p773_3 := h773c.2.2.2
                                  linarith only [hlam, p773_0]
                          · linarith only [h4, h705, h709, h712, h716, h767, h768, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h4, h705, h709, h712, h716, h767, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h708, h710, h712, h715, hc24, hlam, hphi, ht45, u5elo0]
                  · linarith only [h707, h710, h713, h714, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h4, h706, h713, hc12, hc23, hlam, hphi]
              · linarith only [h4, h705, h712, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
            · linarith only [h4, h706, h821, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
              · rcases m.htr 1 2 5 (by decide) (by decide) with h824 | h824
                · rcases m.htr 1 3 4 (by decide) (by decide) with h825 | h825
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h826 | h826
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h827 | h827
                      · linarith only [h2, h709, h827, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h829 | h829
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h830 | h830
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h831 | h831
                            · linarith only [h2, h4, h705, h709, h831, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h833 | h833
                              · linarith only [h4, h705, h709, h829, h833, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi5]
                              · rcases h2bigk with h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h4, h824, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p835_1, u5ehi8]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h4, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 2) (by simp) with h839 | h839
                                  · rcases p835_3 (m.d 1 2) (by simp) with h840 | h840
                                    · linarith only [h0, h840, hlam]
                                    · linarith only [h823, h840, hlam]
                                  · linarith only [h839, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h4, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p835_1, u5ehi8]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h821, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 2) (by simp) with h848 | h848
                                  · rcases p835_3 (m.d 1 2) (by simp) with h849 | h849
                                    · rcases p835_3 (m.d 2 3) (by simp) with h850 | h850
                                      · rcases p835_3 (m.d 2 4) (by simp) with h851 | h851
                                        · linarith only [h851, hlam, p835_0]
                                        · rcases p835_3 (m.d 2 5) (by simp) with h853 | h853
                                          · linarith only [h824, h853, hlam]
                                          · linarith only [h831, h853, hlam]
                                      · linarith only [h829, h850, hlam]
                                    · linarith only [h849, hlam, p835_0]
                                  · linarith only [h705, h848, hlam]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, h4, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p835_1, u5ehi8]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h706, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p835_1, u5ehi8]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h824, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p835_1, u5ehi8]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 2) (by simp) with h863 | h863
                                  · linarith only [h4, h863, hlam]
                                  · linarith only [h705, h863, hlam]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 2) (by simp) with h866 | h866
                                  · linarith only [h4, h866, hlam]
                                  · linarith only [h706, h866, hlam]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h705, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h823, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h829, hlam, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h831, hlam, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h706, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h824, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h830, hlam, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h3, h824, hc24, hlam, hphi, ht45, p835_1, u5elo0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                          · linarith only [h0, h4, h824, h830, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h4, h824, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h821, h824, h826, hlam, hphi, u5ehi7, u5elo3]
                  · linarith only [h707, h821, h824, h825, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h4, h706, h824, hc12, hc23, hlam, hphi]
              · linarith only [h4, h705, h823, hc12, hc23, hlam, hphi]
        · linarith only [h4, h705, h708, hc24, hlam, hphi, ht45, u5elo3]
      · linarith only [h4, h705, h707, hlam]
    · linarith only [h705, h706, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h888 | h888
    · rcases m.htr 0 3 4 (by decide) (by decide) with h889 | h889
      · rcases m.htr 0 3 5 (by decide) (by decide) with h890 | h890
        · rcases m.htr 0 4 5 (by decide) (by decide) with h891 | h891
          · rcases m.htr 1 2 3 (by decide) (by decide) with h892 | h892
            · linarith only [h0, h4, h892, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h894 | h894
              · linarith only [h0, h705, h894, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h896 | h896
                · rcases m.htr 1 3 4 (by decide) (by decide) with h897 | h897
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h898 | h898
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h899 | h899
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h900 | h900
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h901 | h901
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h902 | h902
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h903 | h903
                              · linarith only [h1, h897, h903, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · rcases h2bigk with h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c | h905c
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h896, h902, h903, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h4, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h705, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h705, h900, h902, h903, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h0, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h892, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h894, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h0, h902, h903, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h888, h902, h903, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h896, h902, h903, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h705, h888, h902, h903, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  rcases p905_3 (m.d 0 2) (by simp) with h920 | h920
                                  · linarith only [h4, h920, hlam]
                                  · linarith only [h888, h920, hlam]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h0, h896, h902, h903, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h896, h902, h903, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h900, hlam, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  rcases p905_3 (m.d 0 2) (by simp) with h927 | h927
                                  · linarith only [h705, h927, hlam]
                                  · linarith only [h888, h927, hlam]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h888, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h896, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h901, hlam, p905_1]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [h902, hlam, p905_0]
                                · have p905_0 := h905c.1
                                  have p905_1 := h905c.2.1
                                  have p905_2 := h905c.2.2.1
                                  have p905_3 := h905c.2.2.2
                                  linarith only [hlam, p905_0]
                            · linarith only [h705, h902, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h705, h896, h900, h901, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h4, h896, h900, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h889, h891, h894, h896, h899, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h897, h898, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h889, h892, h896, h897, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h4, h888, h896, hc12, hc23, hlam, hphi]
          · linarith only [h705, h888, h891, hlam, hphi, u5ehi7, u5elo4]
        · linarith only [h4, h888, h890, hlam, hphi, u5ehi7, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h944 | h944
        · rcases m.htr 0 4 5 (by decide) (by decide) with h945 | h945
          · rcases m.htr 1 2 3 (by decide) (by decide) with h946 | h946
            · linarith only [h0, h4, h946, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
              · linarith only [h705, h888, h948, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 3 4 (by decide) (by decide) with h951 | h951
                  · linarith only [h1, h889, h951, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h953 | h953
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h954 | h954
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h955 | h955
                        · linarith only [h0, h4, h889, h950, h955, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h0, h4, h950, h955, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h945, h948, h950, h954, hlam, hphi, u5ehi7, u5elo0]
                    · linarith only [h889, h944, h953, hc13, hc34, hlam, hphi]
                · linarith only [h4, h888, h889, h950, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h705, h888, h945, hlam, hphi, u5ehi7, u5elo4]
        · linarith only [h4, h888, h944, hlam, hphi, u5ehi7, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h963 | h963
      · rcases m.htr 0 3 5 (by decide) (by decide) with h964 | h964
        · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
          · rcases m.htr 1 2 3 (by decide) (by decide) with h966 | h966
            · linarith only [h0, h888, h966, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h968 | h968
              · linarith only [h0, h705, h965, h968, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h970 | h970
                · linarith only [h0, h888, h970, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h973 | h973
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h974 | h974
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h975 | h975
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h976 | h976
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h977 | h977
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h978 | h978
                              · linarith only [h1, h972, h978, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · rcases h2bigk with h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h888, hc12, hlam, hphi, ht23, ht34, ht45, p980_1, u5elo2]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h4, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h705, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h888, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h0, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h966, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h968, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h970, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  rcases p980_3 (m.d 0 2) (by simp) with h991 | h991
                                  · linarith only [h991, hlam, p980_0]
                                  · rcases p980_3 (m.d 1 2) (by simp) with h993 | h993
                                    · linarith only [h966, h993, hlam]
                                    · rcases p980_3 (m.d 2 3) (by simp) with h995 | h995
                                      · rcases p980_3 (m.d 2 4) (by simp) with h996 | h996
                                        · linarith only [h975, h996, hlam]
                                        · linarith only [h705, h996, hlam]
                                      · linarith only [h995, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  rcases p980_3 (m.d 0 2) (by simp) with h1000 | h1000
                                  · linarith only [h1000, h4, hlam]
                                  · linarith only [h0, h1000, hlam]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h2, h705, h974, h978, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p980_1]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h888, hc02, hc23, hlam, hphi, p980_1]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  rcases p980_3 (m.d 0 2) (by simp) with h1006 | h1006
                                  · linarith only [h1006, hlam, p980_0]
                                  · rcases p980_3 (m.d 1 2) (by simp) with h1008 | h1008
                                    · linarith only [h1008, h968, hlam]
                                    · rcases p980_3 (m.d 2 3) (by simp) with h1010 | h1010
                                      · rcases p980_3 (m.d 2 4) (by simp) with h1011 | h1011
                                        · rcases p980_3 (m.d 2 5) (by simp) with h1012 | h1012
                                          · linarith only [h1012, h977, hlam]
                                          · linarith only [h1012, h888, hlam]
                                        · linarith only [h1011, hlam, p980_0]
                                      · linarith only [h1010, h4, hlam]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  rcases p980_3 (m.d 0 2) (by simp) with h1017 | h1017
                                  · linarith only [h1017, h705, hlam]
                                  · linarith only [h0, h1017, hlam]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h975, hlam, p980_1]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h0, h888, hc12, hc24, hlam, hphi, p980_1]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p980_1, u5elo2]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p980_1, u5elo2]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h976, hlam, p980_1]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [h977, hlam, p980_0]
                                · have p980_0 := h980c.1
                                  have p980_1 := h980c.2.1
                                  have p980_2 := h980c.2.2.1
                                  have p980_3 := h980c.2.2.2
                                  linarith only [hlam, p980_0]
                            · linarith only [h0, h705, h977, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h4, h976, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h4, h963, h975, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1031 | h1031
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1032 | h1032
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1033 | h1033
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1034 | h1034
                              · linarith only [h1034, h4, h963, h968, h974, hc12, hc23, hlam, hphi]
                              · rcases h2bigk with h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h4, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h705, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h888, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h0, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h966, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h968, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h970, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  rcases p1036_3 (m.d 0 2) (by simp) with h1047 | h1047
                                  · linarith only [h1047, hlam, p1036_0]
                                  · rcases p1036_3 (m.d 1 2) (by simp) with h1049 | h1049
                                    · linarith only [h1049, h966, hlam]
                                    · rcases p1036_3 (m.d 2 3) (by simp) with h1051 | h1051
                                      · rcases p1036_3 (m.d 2 4) (by simp) with h1052 | h1052
                                        · linarith only [h1031, h1052, hlam]
                                        · linarith only [h1052, h705, hlam]
                                      · linarith only [h1051, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  rcases p1036_3 (m.d 0 2) (by simp) with h1056 | h1056
                                  · linarith only [h1056, h4, hlam]
                                  · linarith only [h0, h1056, hlam]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h705, h965, h968, h974, hc12, hc23, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h888, h965, h968, h974, hc12, hc23, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  rcases p1036_3 (m.d 0 2) (by simp) with h1062 | h1062
                                  · linarith only [h1062, hlam, p1036_0]
                                  · rcases p1036_3 (m.d 1 2) (by simp) with h1064 | h1064
                                    · linarith only [h1064, h968, hlam]
                                    · rcases p1036_3 (m.d 2 3) (by simp) with h1066 | h1066
                                      · rcases p1036_3 (m.d 2 4) (by simp) with h1067 | h1067
                                        · rcases p1036_3 (m.d 2 5) (by simp) with h1068 | h1068
                                          · linarith only [h1033, h1068, hlam]
                                          · linarith only [h1068, h888, hlam]
                                        · linarith only [h1067, hlam, p1036_0]
                                      · linarith only [h1066, h4, hlam]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  rcases p1036_3 (m.d 0 2) (by simp) with h1073 | h1073
                                  · linarith only [h1073, h705, hlam]
                                  · linarith only [h0, h1073, hlam]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1031, hlam, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h888, h965, h968, h974, hc12, hc24, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p1036_1, u5elo2]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1036_1, u5elo2]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1032, hlam, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1033, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                            · linarith only [h0, h1033, h705, h888, h965, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                          · linarith only [h1, h1032, h4, h973, hlam]
                        · linarith only [h1031, h4, h963, h965, h972, h974, hlam]
                    · linarith only [h888, h964, h972, h973, hc34, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1088 | h1088
                    · linarith only [h1088, h963, h972, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1092 | h1092
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1093 | h1093
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1094 | h1094
                              · rcases h2bigk with h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p1095_1]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h4, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h705, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h888, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h0, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h966, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h968, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h970, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  rcases p1095_3 (m.d 0 2) (by simp) with h1106 | h1106
                                  · linarith only [h1106, hlam, p1095_0]
                                  · rcases p1095_3 (m.d 1 2) (by simp) with h1108 | h1108
                                    · linarith only [h1108, h966, hlam]
                                    · rcases p1095_3 (m.d 2 3) (by simp) with h1110 | h1110
                                      · rcases p1095_3 (m.d 2 4) (by simp) with h1111 | h1111
                                        · linarith only [h1091, h1111, hlam]
                                        · linarith only [h1111, h705, hlam]
                                      · linarith only [h1110, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  rcases p1095_3 (m.d 0 2) (by simp) with h1115 | h1115
                                  · linarith only [h1115, h4, hlam]
                                  · linarith only [h0, h1115, hlam]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h1088, h1090, h705, h888, h963, h964, h966, h972, hc12, hc23, hlam, hphi, p1095_1, u5ehi9, u5elo2]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h1088, h888, h964, h966, hc12, hc23, hlam, hphi, p1095_1]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  rcases p1095_3 (m.d 0 2) (by simp) with h1121 | h1121
                                  · linarith only [h1121, hlam, p1095_0]
                                  · rcases p1095_3 (m.d 1 2) (by simp) with h1123 | h1123
                                    · linarith only [h1123, h968, hlam]
                                    · rcases p1095_3 (m.d 2 3) (by simp) with h1125 | h1125
                                      · rcases p1095_3 (m.d 2 4) (by simp) with h1126 | h1126
                                        · rcases p1095_3 (m.d 2 5) (by simp) with h1127 | h1127
                                          · linarith only [h1093, h1127, hlam]
                                          · linarith only [h1127, h888, hlam]
                                        · linarith only [h1126, hlam, p1095_0]
                                      · linarith only [h1125, h4, hlam]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  rcases p1095_3 (m.d 0 2) (by simp) with h1132 | h1132
                                  · linarith only [h1132, h705, hlam]
                                  · linarith only [h0, h1132, hlam]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h1091, hlam, p1095_1]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h1088, h888, h964, h966, hc12, hc24, hlam, hphi, p1095_1]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p1095_1, u5elo2]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1095_1, u5elo2]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h1092, hlam, p1095_1]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [h1093, hlam, p1095_0]
                                · have p1095_0 := h1095c.1
                                  have p1095_1 := h1095c.2.1
                                  have p1095_2 := h1095c.2.2.1
                                  have p1095_3 := h1095c.2.2.2
                                  linarith only [hlam, p1095_0]
                              · linarith only [h1090, h1094, h972, hlam]
                            · linarith only [h0, h1090, h1093, h705, h972, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1092, h4, h888, h963, h964, h972, hc14, hlam, hphi, ht45, u5elo2]
                        · linarith only [h1091, h4, h963, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1147 | h1147
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1148 | h1148
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1149 | h1149
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
                              · linarith only [h1090, h1150, h4, h963, h966, h972, hc12, hc23, hlam, hphi]
                              · linarith only [h1150, h705, h965, h966, h972, hc12, hc24, hlam, hphi]
                            · linarith only [h0, h1149, h705, h888, h965, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                          · linarith only [h0, h1148, h4, h888, h964, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1090, h1147, h4, h963, h965, h966, h972, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1156 | h1156
            · linarith only [h0, h1156, h4, h705, h964, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
              · linarith only [h0, h1158, h705, h965, hc24, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1160 | h1160
                · linarith only [h0, h1160, h705, h888, h965, hlam, hphi, u5ehi5, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1162 | h1162
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1163 | h1163
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1164 | h1164
                      · linarith only [h1164, h2, h965, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1166 | h1166
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1167 | h1167
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1168 | h1168
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1169 | h1169
                              · linarith only [h0, h1169, h4, h705, h963, h965, hc12, hc23, hlam, hphi]
                              · rcases h2bigk with h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1168, h705, h965, hc12, hlam, hphi, ht23, ht34, ht45, p1171_1, u5elo2]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h4, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h705, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h888, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h0, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1156, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1158, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1160, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  rcases p1171_3 (m.d 0 2) (by simp) with h1182 | h1182
                                  · linarith only [h1182, hlam, p1171_0]
                                  · rcases p1171_3 (m.d 1 2) (by simp) with h1184 | h1184
                                    · linarith only [h1156, h1184, hlam]
                                    · rcases p1171_3 (m.d 2 3) (by simp) with h1186 | h1186
                                      · rcases p1171_3 (m.d 2 4) (by simp) with h1187 | h1187
                                        · linarith only [h1166, h1187, hlam]
                                        · linarith only [h1187, h705, hlam]
                                      · linarith only [h1186, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  rcases p1171_3 (m.d 0 2) (by simp) with h1191 | h1191
                                  · linarith only [h1191, h4, hlam]
                                  · linarith only [h0, h1191, hlam]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1168, h705, h965, hc02, hc23, hlam, hphi, p1171_1]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h0, h888, hc12, hc23, hlam, hphi, p1171_1]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  rcases p1171_3 (m.d 0 2) (by simp) with h1197 | h1197
                                  · linarith only [h1197, hlam, p1171_0]
                                  · rcases p1171_3 (m.d 1 2) (by simp) with h1199 | h1199
                                    · linarith only [h1158, h1199, hlam]
                                    · rcases p1171_3 (m.d 2 3) (by simp) with h1201 | h1201
                                      · rcases p1171_3 (m.d 2 4) (by simp) with h1202 | h1202
                                        · rcases p1171_3 (m.d 2 5) (by simp) with h1203 | h1203
                                          · linarith only [h1168, h1203, hlam]
                                          · linarith only [h1203, h888, hlam]
                                        · linarith only [h1202, hlam, p1171_0]
                                      · linarith only [h1201, h4, hlam]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  rcases p1171_3 (m.d 0 2) (by simp) with h1208 | h1208
                                  · linarith only [h1208, h705, hlam]
                                  · linarith only [h0, h1208, hlam]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1166, hlam, p1171_1]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h0, h1168, h705, h965, hc12, hc24, hlam, hphi, p1171_1]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1171_1, u5elo2]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1171_1, u5elo2]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1167, hlam, p1171_1]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [h1168, hlam, p1171_0]
                                · have p1171_0 := h1171c.1
                                  have p1171_1 := h1171c.2.1
                                  have p1171_2 := h1171c.2.2.1
                                  have p1171_3 := h1171c.2.2.2
                                  linarith only [hlam, p1171_0]
                            · linarith only [h0, h1168, h705, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1, h1163, h1167, h4, hlam]
                        · linarith only [h1, h1162, h1163, h1166, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · linarith only [h1162, h1163, h888, h964, hc34, hlam, hphi, ht45, u5elo2]
                  · linarith only [h1162, h963, h965, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h963, h964, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1225 | h1225
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1226 | h1226
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1227 | h1227
            · linarith only [h0, h1225, h1227, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
              · linarith only [h0, h1225, h1229, h705, h888, h963, hlam, hphi, u5ehi8, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1231 | h1231
                · linarith only [h0, h1231, h888, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1233 | h1233
                  · linarith only [h1225, h1233, h963, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1237 | h1237
                        · linarith only [h1, h1235, h1237, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1239 | h1239
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1240 | h1240
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1241 | h1241
                              · rcases h2bigk with h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h888, hc12, hlam, hphi, ht23, ht34, ht45, p1242_1, u5elo2]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h4, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h705, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h888, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h0, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1227, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1229, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1231, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1237, hc02, hc34, hlam, hphi, ht23, p1242_1]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1237, hc12, hc34, hlam, hphi, ht23, p1242_1]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1237, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1237, h888, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1242_1, u5ehi5]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  rcases p1242_3 (m.d 0 2) (by simp) with h1258 | h1258
                                  · linarith only [h1258, hlam, p1242_0]
                                  · rcases p1242_3 (m.d 1 2) (by simp) with h1260 | h1260
                                    · linarith only [h1229, h1260, hlam]
                                    · rcases p1242_3 (m.d 2 3) (by simp) with h1262 | h1262
                                      · linarith only [h1237, h1262, hlam]
                                      · linarith only [h1262, h4, hlam]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  rcases p1242_3 (m.d 0 2) (by simp) with h1265 | h1265
                                  · linarith only [h1265, h705, hlam]
                                  · linarith only [h0, h1265, hlam]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1, h1235, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1242_1, u5ehi8]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h0, h1237, h888, hc12, hc34, hlam, hphi, ht23, p1242_1]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1242_1, u5elo2]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1, h1235, h1241, h963, hc12, hc34, hlam, hphi, ht23, p1242_1, u5ehi9, u5elo2]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1239, hlam, p1242_1]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [h1240, hlam, p1242_0]
                                · have p1242_0 := h1242c.1
                                  have p1242_1 := h1242c.2.1
                                  have p1242_2 := h1242c.2.2.1
                                  have p1242_3 := h1242c.2.2.2
                                  linarith only [hlam, p1242_0]
                              · linarith only [h1, h1235, h1237, h1241, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                            · linarith only [h0, h1240, h705, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1, h1235, h1239, h4, hlam]
                      · linarith only [h1226, h1233, h1235, h1236, h888, hlam, hphi, u5ehi8, u5elo2]
                    · linarith only [h1225, h1235, h963, hc13, hc34, hlam, hphi]
          · linarith only [h1225, h1226, h963, hlam, hphi, u5ehi8, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1282 | h1282
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1283 | h1283
            · linarith only [h0, h1283, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1285 | h1285
              · linarith only [h0, h1282, h1285, h4, h705, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1287 | h1287
                · linarith only [h1, h1225, h1283, h1287, h888, hlam, hphi, u5ehi5, u5elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1289 | h1289
                  · linarith only [h1, h1225, h1289, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1291 | h1291
                    · linarith only [h1, h1225, h1291, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1293 | h1293
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1295 | h1295
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1296 | h1296
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1297 | h1297
                              · rcases h2bigk with h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1225, h1295, h4, hc12, hlam, hphi, ht23, ht34, ht45, p1298_1, u5elo2]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h4, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h705, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h888, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h0, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1283, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1285, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1287, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  rcases p1298_3 (m.d 0 2) (by simp) with h1309 | h1309
                                  · linarith only [h1309, hlam, p1298_0]
                                  · rcases p1298_3 (m.d 1 2) (by simp) with h1311 | h1311
                                    · linarith only [h1283, h1311, hlam]
                                    · rcases p1298_3 (m.d 2 3) (by simp) with h1313 | h1313
                                      · rcases p1298_3 (m.d 2 4) (by simp) with h1314 | h1314
                                        · linarith only [h1294, h1314, hlam]
                                        · linarith only [h1314, h705, hlam]
                                      · linarith only [h1313, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  rcases p1298_3 (m.d 0 2) (by simp) with h1318 | h1318
                                  · linarith only [h1318, h4, hlam]
                                  · linarith only [h0, h1318, hlam]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1293, h1294, h2, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1298_1, u5ehi9]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h0, h1225, h1295, h4, hc12, hc23, hlam, hphi, p1298_1]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  rcases p1298_3 (m.d 0 2) (by simp) with h1324 | h1324
                                  · linarith only [h1324, hlam, p1298_0]
                                  · rcases p1298_3 (m.d 1 2) (by simp) with h1326 | h1326
                                    · linarith only [h1285, h1326, hlam]
                                    · rcases p1298_3 (m.d 2 3) (by simp) with h1328 | h1328
                                      · rcases p1298_3 (m.d 2 4) (by simp) with h1329 | h1329
                                        · rcases p1298_3 (m.d 2 5) (by simp) with h1330 | h1330
                                          · linarith only [h1296, h1330, hlam]
                                          · linarith only [h1330, h888, hlam]
                                        · linarith only [h1329, hlam, p1298_0]
                                      · linarith only [h1328, h4, hlam]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  rcases p1298_3 (m.d 0 2) (by simp) with h1335 | h1335
                                  · linarith only [h1335, h705, hlam]
                                  · linarith only [h0, h1335, hlam]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1294, hlam, p1298_1]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h0, h1225, h1295, h4, hc12, hc24, hlam, hphi, p1298_1]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1298_1, u5elo2]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1298_1, u5elo2]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1295, hlam, p1298_1]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [h1296, hlam, p1298_0]
                                · have p1298_0 := h1298c.1
                                  have p1298_1 := h1298c.2.1
                                  have p1298_2 := h1298c.2.2.1
                                  have p1298_3 := h1298c.2.2.2
                                  linarith only [hlam, p1298_0]
                              · linarith only [h1293, h1297, h2, h963, hlam]
                            · linarith only [h0, h1293, h1296, h2, h705, h963, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1294, h1295, h963, hc04, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1349 | h1349
                          · linarith only [h1, h1225, h1294, h1349, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h1349, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1352 | h1352
                        · linarith only [h1282, h1285, h1293, h1352, h963, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1354 | h1354
                          · linarith only [h0, h1225, h1352, h1354, h4, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1354, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1357 | h1357
            · linarith only [h0, h1357, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1359 | h1359
              · linarith only [h0, h1359, h705, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1361 | h1361
                · linarith only [h0, h1282, h1361, h3, h705, h888, hlam, hphi, u5ehi6, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
                  · linarith only [h1, h1282, h1363, h963, hc34, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1365 | h1365
                    · linarith only [h1, h1282, h1365, h963, hlam, hphi, u5ehi8, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1367 | h1367
                      · linarith only [h1282, h1367, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1369 | h1369
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1370 | h1370
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1371 | h1371
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1372 | h1372
                              · linarith only [h0, h1282, h1369, h1372, h4, h963, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1371, h1372, h4, h963, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                            · linarith only [h0, h1371, h705, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h1370, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1377 | h1377
                          · linarith only [h0, h1225, h1369, h1377, h4, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1377, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1381 | h1381
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1382 | h1382
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1383 | h1383
      · linarith only [h0, h1383, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1385 | h1385
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1386 | h1386
          · linarith only [h1, h1386, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1388 | h1388
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1389 | h1389
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1391 | h1391
                  · linarith only [h1382, h1383, h1388, h1391, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1393 | h1393
                    · linarith only [h0, h1391, h1393, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · linarith only [h0, h1385, h1391, h1393, h2, hc12, hc24, hlam, hphi]
                · linarith only [h1382, h1383, h1390, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1382, h1389, h2, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1398 | h1398
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1399 | h1399
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1400 | h1400
                  · linarith only [h0, h1383, h1385, h1400, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1402 | h1402
                    · linarith only [h0, h1400, h1402, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · linarith only [h1399, h1402, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h1382, h1388, h1399, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h1398, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h1382, h1385, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1408 | h1408
      · linarith only [h0, h1408, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1410 | h1410
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1411 | h1411
          · linarith only [h1, h1411, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1413 | h1413
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1414 | h1414
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
                · linarith only [h1382, h1410, h1415, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1417 | h1417
                  · linarith only [h1408, h1410, h1417, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1419 | h1419
                    · linarith only [h1, h1415, h1417, h1419, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · linarith only [h1, h1382, h1410, h1417, h1419, h2, hc12, hc24, hlam, hphi]
              · linarith only [h1, h1414, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h1382, h1410, h1413, hlam, hphi, u5ehi7, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1424 | h1424
          · linarith only [h1, h1424, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1426 | h1426
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1427 | h1427
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                · linarith only [h0, h1382, h1426, h1428, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                  · linarith only [h0, h1410, h1430, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h0, h1410, h1432, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1434 | h1434
                      · linarith only [h1, h1424, h1434, h2, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1436 | h1436
                        · linarith only [h1, h1434, h1436, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h1, h1426, h1434, h1436, h2, hc13, hc34, hlam, hphi]
              · linarith only [h0, h1427, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1440 | h1440
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
                · linarith only [h0, h1382, h1441, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1443 | h1443
                  · linarith only [h1, h1426, h1441, h1443, hc24, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1445 | h1445
                    · linarith only [h1, h1426, h1441, h1445, hlam, hphi, u5ehi7, u5elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
                      · linarith only [h1, h1426, h1447, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1449 | h1449
                        · linarith only [h1, h1426, h1449, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1451 | h1451
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1452 | h1452
                            · linarith only [h0, h1447, h1452, h2, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1454 | h1454
                              · linarith only [h1382, h1426, h1452, h1454, hc02, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1382, h1454, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h1381, h1451, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
              · linarith only [h1381, h1440, h2, hlam, hphi, u5ehi6, u5elo4]
  · linarith only [h0, h1381, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

end R2N4
