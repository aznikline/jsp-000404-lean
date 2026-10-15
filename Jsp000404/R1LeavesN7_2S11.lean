import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S7
import Jsp000404.R1LeavesN7_2S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h4388 | h4388
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 13924000 in
set_option maxHeartbeats 13924000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6829 | h6829
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6830 | h6830
      · linarith only [h4, h6, h6830, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6832 | h6832
        · linarith only [h5, h6, h6832, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6834 | h6834
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6835 | h6835
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6836 | h6836
              · linarith only [h0, h4, h6, h6829, h6836, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6838 | h6838
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6839 | h6839
                  · linarith only [h1, h6830, h6839, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6841 | h6841
                    · linarith only [h2, h6832, h6841, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6843 | h6843
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6844 | h6844
                        · linarith only [h0, h6, h6830, h6834, h6844, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6846 | h6846
                          · linarith only [h0, h2, h6, h6832, h6834, h6835, h6843, h6846, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h6, h6834, h6843, h6846, hc34, hc45, hlam, hphi]
                      · linarith only [h6829, h6830, h6843, hc23, hc35, hlam, hphi]
                · linarith only [h6829, h6830, h6834, h6838, hc23, hc35, hlam, hphi]
            · linarith only [h5, h6, h6834, h6835, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h4, h6, h6834, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6853 | h6853
      · linarith only [h4, h6, h6853, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6855 | h6855
        · linarith only [h5, h6, h6855, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6857 | h6857
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6858 | h6858
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6859 | h6859
              · linarith only [h0, h6, h6859, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6861 | h6861
                · linarith only [h1, h6829, h6861, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6863 | h6863
                  · linarith only [h0, h1, h6, h6829, h6853, h6857, h6863, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6865 | h6865
                    · linarith only [h2, h6855, h6865, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6867 | h6867
                      · linarith only [h1, h6829, h6857, h6867, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6869 | h6869
                        · linarith only [h0, h6, h6853, h6858, h6867, h6869, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6871 | h6871
                          · linarith only [h0, h2, h6, h6855, h6858, h6871, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6873 | h6873
                            · linarith only [h0, h6, h6858, h6867, h6871, h6873, hc23, hc34, hlam, hphi]
                            · rcases h0bigk with h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c | h6875c
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                rcases p6875_3 (m.d 0 1) (by simp) with h6877 | h6877
                                · rcases p6875_3 (m.d 0 2) (by simp) with h6878 | h6878
                                  · linarith only [h0, h6878, hlam]
                                  · rcases p6875_3 (m.d 0 3) (by simp) with h6880 | h6880
                                    · linarith only [h1, h6880, hlam]
                                    · rcases p6875_3 (m.d 0 4) (by simp) with h6882 | h6882
                                      · linarith only [h2, h6882, hlam]
                                      · rcases p6875_3 (m.d 0 5) (by simp) with h6884 | h6884
                                        · linarith only [h3, h6884, hlam]
                                        · linarith only [h6, h6884, hlam]
                                · linarith only [h0, h6877, hlam]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                rcases p6875_3 (m.d 0 1) (by simp) with h6888 | h6888
                                · rcases p6875_3 (m.d 0 2) (by simp) with h6889 | h6889
                                  · linarith only [h0, h6889, hlam]
                                  · linarith only [h4, h6889, hlam]
                                · linarith only [h1, h6888, hlam]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                rcases p6875_3 (m.d 0 1) (by simp) with h6893 | h6893
                                · rcases p6875_3 (m.d 0 2) (by simp) with h6894 | h6894
                                  · linarith only [h0, h6894, hlam]
                                  · linarith only [h5, h6894, hlam]
                                · linarith only [h2, h6893, hlam]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                rcases p6875_3 (m.d 0 1) (by simp) with h6898 | h6898
                                · rcases p6875_3 (m.d 0 2) (by simp) with h6899 | h6899
                                  · linarith only [h0, h6899, hlam]
                                  · rcases p6875_3 (m.d 0 3) (by simp) with h6901 | h6901
                                    · linarith only [h1, h6901, hlam]
                                    · rcases p6875_3 (m.d 0 4) (by simp) with h6903 | h6903
                                      · linarith only [h2, h6903, hlam]
                                      · rcases p6875_3 (m.d 0 5) (by simp) with h6905 | h6905
                                        · linarith only [h3, h6905, hlam]
                                        · rcases h2bigk with h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c | h6907c
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6, h6858, h6867, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6875_1, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6875_1, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6, h6867, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6875_1, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h0, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6875_1, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h0, h6, h6867, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6875_1, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6859, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h4, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6857, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6867, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6869, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h5, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6858, hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6875_1, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [hlam, p6907_0]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6871, hlam, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h0, h6858, h6869, h6873, hc24, hc45, hlam, hphi, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [h6857, h6869, h6873, hc23, hc45, hlam, hphi, ht34, p6907_1]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            rcases p6907_3 (m.d 0 2) (by simp) with h6930 | h6930
                                            · linarith only [h6, h6930, hlam]
                                            · linarith only [h4, h6930, hlam]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            rcases p6907_3 (m.d 0 2) (by simp) with h6933 | h6933
                                            · linarith only [h6, h6933, hlam]
                                            · linarith only [h5, h6933, hlam]
                                          · have p6907_0 := h6907c.1
                                            have p6907_1 := h6907c.2.1
                                            have p6907_2 := h6907c.2.2.1
                                            have p6907_3 := h6907c.2.2.2
                                            linarith only [hlam, p6907_0]
                                · linarith only [h3, h6898, hlam]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h0, hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h6, h6869, h6873, hc03, hc45, hlam, hphi, ht34, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h1, h6, h6829, h6869, h6873, hc13, hc45, hlam, hphi, ht34, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h6, hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h1, hlam, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h4, hlam, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h6829, hlam, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h6853, hlam, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h2, hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h5, hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h1, h5, h6, h6869, h6873, hc13, hc45, hlam, hphi, ht34, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h6855, hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h3, hlam, p6875_0]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [h0, h6, h6858, h6867, h6869, h6873, hc23, hc45, hlam, hphi, ht34, p6875_1]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                rcases p6875_3 (m.d 0 1) (by simp) with h6955 | h6955
                                · rcases p6875_3 (m.d 0 2) (by simp) with h6956 | h6956
                                  · linarith only [h6, h6956, hlam]
                                  · linarith only [h4, h6956, hlam]
                                · linarith only [h1, h6955, hlam]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                rcases p6875_3 (m.d 0 1) (by simp) with h6960 | h6960
                                · rcases p6875_3 (m.d 0 2) (by simp) with h6961 | h6961
                                  · linarith only [h6, h6961, hlam]
                                  · linarith only [h5, h6961, hlam]
                                · linarith only [h2, h6960, hlam]
                              · have p6875_0 := h6875c.1
                                have p6875_1 := h6875c.2.1
                                have p6875_2 := h6875c.2.2.1
                                have p6875_3 := h6875c.2.2.2
                                linarith only [hlam, p6875_0]
            · linarith only [h5, h6, h6858, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h6857, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 14664000 in
set_option maxHeartbeats 14664000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_23_L_I_L_I_H_I_s5 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6968 | h6968
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6969 | h6969
      · linarith only [h4, h5, h6969, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6971 | h6971
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6972 | h6972
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6973 | h6973
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6974 | h6974
              · linarith only [h0, h5, h6974, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6976 | h6976
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6977 | h6977
                  · linarith only [h1, h6969, h6971, h6977, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6979 | h6979
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6980 | h6980
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6981 | h6981
                        · linarith only [h4, h5, h6969, h6981, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6983 | h6983
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6984 | h6984
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6985 | h6985
                              · rcases h0bigk with h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c | h6986c
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h0, h6973, h6983, h6985, hc01, hc45, hlam, hphi, ht0b, ht5b, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  rcases p6986_3 (m.d 0 1) (by simp) with h6989 | h6989
                                  · rcases p6986_3 (m.d 0 2) (by simp) with h6990 | h6990
                                    · linarith only [h0, h6990, hlam]
                                    · linarith only [h4, h6990, hlam]
                                  · linarith only [h1, h6989, hlam]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h0, h5, h6973, h6983, h6985, hc01, hc45, hlam, hphi, ht0b, ht5b, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  rcases p6986_3 (m.d 0 1) (by simp) with h6995 | h6995
                                  · rcases p6986_3 (m.d 0 2) (by simp) with h6996 | h6996
                                    · linarith only [h0, h6996, hlam]
                                    · linarith only [h6968, h6996, hlam]
                                  · linarith only [h3, h6995, hlam]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h0, hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h5, h6981, hc03, hc34, hlam, hphi, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h5, hlam, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  rcases p6986_3 (m.d 0 1) (by simp) with h7004 | h7004
                                  · rcases p6986_3 (m.d 0 2) (by simp) with h7005 | h7005
                                    · rcases p6986_3 (m.d 0 3) (by simp) with h7006 | h7006
                                      · linarith only [h4, h7006, hlam]
                                      · linarith only [h6971, h7006, hlam]
                                    · linarith only [h6968, h7005, hlam]
                                  · linarith only [h3, h7004, hlam]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h1, hlam, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h4, hlam, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h6969, hlam, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  rcases p6986_3 (m.d 0 1) (by simp) with h7015 | h7015
                                  · rcases p6986_3 (m.d 0 2) (by simp) with h7016 | h7016
                                    · rcases p6986_3 (m.d 0 3) (by simp) with h7017 | h7017
                                      · rcases p6986_3 (m.d 0 4) (by simp) with h7018 | h7018
                                        · rcases p6986_3 (m.d 0 5) (by simp) with h7019 | h7019
                                          · linarith only [h6971, h7019, hlam]
                                          · rcases h2bigk with h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c | h7021c
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h5, h6981, hc12, hc34, hlam, hphi, ht23, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h5, h6981, hc23, hc34, hlam, hphi, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h5, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              rcases p7021_3 (m.d 0 2) (by simp) with h7026 | h7026
                                              · rcases p7021_3 (m.d 1 2) (by simp) with h7027 | h7027
                                                · linarith only [h0, h7027, hlam]
                                                · linarith only [h6976, h7027, hlam]
                                              · linarith only [h7026, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h0, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h0, h6983, h6985, hc01, hc45, hlam, hphi, ht0b, ht5b, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6974, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              rcases p7021_3 (m.d 0 2) (by simp) with h7035 | h7035
                                              · rcases p7021_3 (m.d 1 2) (by simp) with h7036 | h7036
                                                · rcases p7021_3 (m.d 2 3) (by simp) with h7037 | h7037
                                                  · linarith only [h6973, h7037, hlam]
                                                  · linarith only [h6983, h7037, hlam]
                                                · linarith only [h7036, hlam, p7021_0]
                                              · linarith only [h6968, h7035, hlam]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h4, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6973, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6981, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h4, h5, h6981, h6983, h6985, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h4, h6981, hc23, hc34, hlam, hphi, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6973, h6981, hc23, hc34, hlam, hphi, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              rcases p7021_3 (m.d 0 2) (by simp) with h7049 | h7049
                                              · linarith only [h5, h7049, hlam]
                                              · linarith only [h4, h7049, hlam]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h3, h4, h5, h6976, hlam, p6986_1, p7021_2]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6968, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6976, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6983, hlam, p7021_1]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [h6984, hlam, p7021_0]
                                            · have p7021_0 := h7021c.1
                                              have p7021_1 := h7021c.2.1
                                              have p7021_2 := h7021c.2.2.1
                                              have p7021_3 := h7021c.2.2.2
                                              linarith only [hlam, p7021_0]
                                        · linarith only [h6972, h7018, hlam]
                                      · linarith only [h6971, h7017, hlam]
                                    · linarith only [h6968, h7016, hlam]
                                  · linarith only [h3, h7015, hlam]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h2, hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h0, h6973, h6983, h6985, hc04, hc45, hlam, hphi, ht0b, ht5b, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  rcases p6986_3 (m.d 0 1) (by simp) with h7065 | h7065
                                  · rcases p6986_3 (m.d 0 2) (by simp) with h7066 | h7066
                                    · linarith only [h5, h7066, hlam]
                                    · linarith only [h4, h7066, hlam]
                                  · linarith only [h1, h7065, hlam]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  rcases p6986_3 (m.d 0 1) (by simp) with h7071 | h7071
                                  · rcases p6986_3 (m.d 0 2) (by simp) with h7072 | h7072
                                    · linarith only [h5, h7072, hlam]
                                    · linarith only [h6968, h7072, hlam]
                                  · linarith only [h3, h7071, hlam]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h3, hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h6968, hlam, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h6971, hlam, p6986_0]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [h6972, hlam, p6986_1]
                                · have p6986_0 := h6986c.1
                                  have p6986_1 := h6986c.2.1
                                  have p6986_2 := h6986c.2.2.1
                                  have p6986_3 := h6986c.2.2.2
                                  linarith only [hlam, p6986_0]
                              · linarith only [h0, h5, h6973, h6981, h6983, h6985, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h2, h5, h6973, h6980, h6983, h6984, hc04, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h4, h5, h6971, h6981, h6983, hc23, hc34, hlam, hphi]
                      · linarith only [h6969, h6971, h6972, h6973, h6974, h6980, hc23, hc34, hlam, hphi]
                    · linarith only [h6969, h6971, h6979, hc13, hc34, hlam, hphi]
                · linarith only [h5, h6968, h6973, h6976, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h4, h5, h6973, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h6971, h6972, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7089 | h7089
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7090 | h7090
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7091 | h7091
              · linarith only [h0, h5, h7091, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7093 | h7093
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7094 | h7094
                  · linarith only [h1, h2, h6969, h6971, h7090, h7091, h7094, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7096 | h7096
                    · linarith only [h1, h6971, h7096, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7098 | h7098
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7099 | h7099
                        · linarith only [h4, h5, h6969, h7099, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7101 | h7101
                          · linarith only [h1, h6971, h7090, h7101, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7103 | h7103
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7104 | h7104
                              · rcases h0bigk with h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c | h7105c
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  rcases p7105_3 (m.d 0 1) (by simp) with h7107 | h7107
                                  · rcases p7105_3 (m.d 0 2) (by simp) with h7108 | h7108
                                    · linarith only [h0, h7108, hlam]
                                    · rcases p7105_3 (m.d 0 3) (by simp) with h7110 | h7110
                                      · linarith only [h1, h7110, hlam]
                                      · rcases p7105_3 (m.d 0 4) (by simp) with h7112 | h7112
                                        · linarith only [h2, h7112, hlam]
                                        · linarith only [h5, h7112, hlam]
                                  · linarith only [h0, h7107, hlam]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  rcases p7105_3 (m.d 0 1) (by simp) with h7116 | h7116
                                  · rcases p7105_3 (m.d 0 2) (by simp) with h7117 | h7117
                                    · linarith only [h0, h7117, hlam]
                                    · linarith only [h4, h7117, hlam]
                                  · linarith only [h1, h7116, hlam]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  rcases p7105_3 (m.d 0 1) (by simp) with h7121 | h7121
                                  · rcases p7105_3 (m.d 0 2) (by simp) with h7122 | h7122
                                    · linarith only [h0, h7122, hlam]
                                    · rcases p7105_3 (m.d 0 3) (by simp) with h7124 | h7124
                                      · linarith only [h1, h7124, hlam]
                                      · rcases p7105_3 (m.d 0 4) (by simp) with h7126 | h7126
                                        · linarith only [h2, h7126, hlam]
                                        · rcases p7105_3 (m.d 0 5) (by simp) with h7128 | h7128
                                          · linarith only [h3, h7128, hlam]
                                          · rcases h2bigk with h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c | h7130c
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7105_1, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7105_1, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h5, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h5, h7101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7105_1, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h0, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7105_1, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7091, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h0, h5, h7101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7105_1, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h4, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7090, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7099, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7101, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h4, h7099, hc23, hc34, hlam, hphi, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7090, h7099, hc23, hc34, hlam, hphi, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              rcases p7130_3 (m.d 0 2) (by simp) with h7148 | h7148
                                              · linarith only [h5, h7148, hlam]
                                              · linarith only [h4, h7148, hlam]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              rcases p7130_3 (m.d 0 2) (by simp) with h7152 | h7152
                                              · linarith only [h5, h7152, hlam]
                                              · linarith only [h6968, h7152, hlam]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h6968, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7093, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h0, h7093, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7130_1]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [h7103, hlam, p7130_0]
                                            · have p7130_0 := h7130c.1
                                              have p7130_1 := h7130c.2.1
                                              have p7130_2 := h7130c.2.2.1
                                              have p7130_3 := h7130c.2.2.2
                                              linarith only [hlam, p7130_0]
                                  · linarith only [h2, h7121, hlam]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  rcases p7105_3 (m.d 0 1) (by simp) with h7161 | h7161
                                  · rcases p7105_3 (m.d 0 2) (by simp) with h7162 | h7162
                                    · linarith only [h0, h7162, hlam]
                                    · linarith only [h6968, h7162, hlam]
                                  · linarith only [h3, h7161, hlam]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h0, hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h5, h7099, hc03, hc34, hlam, hphi, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h5, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h1, h5, h6971, h7099, hc13, hc34, hlam, hphi, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h1, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h4, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h6969, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h6971, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h2, hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h4, h5, h7099, hc23, hc34, hlam, hphi, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  rcases p7105_3 (m.d 0 1) (by simp) with h7178 | h7178
                                  · rcases p7105_3 (m.d 0 2) (by simp) with h7179 | h7179
                                    · linarith only [h5, h7179, hlam]
                                    · linarith only [h4, h7179, hlam]
                                  · linarith only [h1, h7178, hlam]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  rcases p7105_3 (m.d 0 1) (by simp) with h7184 | h7184
                                  · rcases p7105_3 (m.d 0 2) (by simp) with h7185 | h7185
                                    · linarith only [h5, h7185, hlam]
                                    · linarith only [h6968, h7185, hlam]
                                  · linarith only [h3, h7184, hlam]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h3, hlam, p7105_0]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h6968, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h1, h5, h6968, h7090, h7099, hc23, hc34, hlam, hphi, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [h7089, hlam, p7105_1]
                                · have p7105_0 := h7105c.1
                                  have p7105_1 := h7105c.2.1
                                  have p7105_2 := h7105c.2.2.1
                                  have p7105_3 := h7105c.2.2.2
                                  linarith only [hlam, p7105_0]
                              · linarith only [h0, h5, h7093, h7099, h7103, h7104, hlam]
                            · linarith only [h4, h5, h7103, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h6969, h7089, h7090, h7091, h7098, hc23, hc34, hlam, hphi]
                · linarith only [h5, h6968, h7090, h7093, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h4, h5, h7090, hc12, hc24, hlam, hphi]
          · linarith only [h5, h6968, h7089, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7200 | h7200
      · linarith only [h4, h5, h7200, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h7202 | h7202
        · linarith only [h4, h6968, h7202, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7204 | h7204
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7205 | h7205
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7206 | h7206
              · linarith only [h0, h5, h7206, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7208 | h7208
                · linarith only [h0, h6968, h7208, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7210 | h7210
                  · linarith only [h1, h7200, h7210, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7212 | h7212
                    · linarith only [h1, h4, h6968, h7202, h7212, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7214 | h7214
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7215 | h7215
                        · linarith only [h4, h5, h7200, h7215, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7217 | h7217
                          · linarith only [h4, h6968, h7202, h7217, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7219 | h7219
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7220 | h7220
                              · rcases h0bigk with h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c | h7221c
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  rcases p7221_3 (m.d 0 1) (by simp) with h7223 | h7223
                                  · rcases p7221_3 (m.d 0 2) (by simp) with h7224 | h7224
                                    · linarith only [h0, h7224, hlam]
                                    · rcases p7221_3 (m.d 0 3) (by simp) with h7226 | h7226
                                      · linarith only [h1, h7226, hlam]
                                      · rcases p7221_3 (m.d 0 4) (by simp) with h7228 | h7228
                                        · linarith only [h2, h7228, hlam]
                                        · linarith only [h5, h7228, hlam]
                                  · linarith only [h0, h7223, hlam]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  rcases p7221_3 (m.d 0 1) (by simp) with h7232 | h7232
                                  · rcases p7221_3 (m.d 0 2) (by simp) with h7233 | h7233
                                    · linarith only [h0, h7233, hlam]
                                    · linarith only [h4, h7233, hlam]
                                  · linarith only [h1, h7232, hlam]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  rcases p7221_3 (m.d 0 1) (by simp) with h7237 | h7237
                                  · rcases p7221_3 (m.d 0 2) (by simp) with h7238 | h7238
                                    · linarith only [h0, h7238, hlam]
                                    · rcases p7221_3 (m.d 0 3) (by simp) with h7240 | h7240
                                      · linarith only [h1, h7240, hlam]
                                      · rcases p7221_3 (m.d 0 4) (by simp) with h7242 | h7242
                                        · linarith only [h2, h7242, hlam]
                                        · rcases p7221_3 (m.d 0 5) (by simp) with h7244 | h7244
                                          · linarith only [h3, h7244, hlam]
                                          · rcases h2bigk with h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c | h7246c
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h6968, h7205, h7219, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h6968, h7204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7221_1, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h5, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h6968, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h0, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h0, h6968, h7204, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7221_1, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7206, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7208, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h4, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7205, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7215, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7217, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h4, h7215, hc23, hc34, hlam, hphi, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7205, h7215, hc23, hc34, hlam, hphi, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              rcases p7246_3 (m.d 0 2) (by simp) with h7264 | h7264
                                              · linarith only [h5, h7264, hlam]
                                              · linarith only [h4, h7264, hlam]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h0, h6968, h7205, h7215, hc23, hc34, hlam, hphi, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h0, h7205, h7217, hc23, hc35, hlam, hphi, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7205, h7217, hc23, hc35, hlam, hphi, p7246_1]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              rcases p7246_3 (m.d 0 2) (by simp) with h7271 | h7271
                                              · linarith only [h6968, h7271, hlam]
                                              · linarith only [h4, h7271, hlam]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [h7219, hlam, p7246_0]
                                            · have p7246_0 := h7246c.1
                                              have p7246_1 := h7246c.2.1
                                              have p7246_2 := h7246c.2.2.1
                                              have p7246_3 := h7246c.2.2.2
                                              linarith only [hlam, p7246_0]
                                  · linarith only [h2, h7237, hlam]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  rcases p7221_3 (m.d 0 1) (by simp) with h7277 | h7277
                                  · rcases p7221_3 (m.d 0 2) (by simp) with h7278 | h7278
                                    · linarith only [h0, h7278, hlam]
                                    · rcases p7221_3 (m.d 0 3) (by simp) with h7280 | h7280
                                      · linarith only [h1, h7280, hlam]
                                      · rcases p7221_3 (m.d 0 4) (by simp) with h7282 | h7282
                                        · linarith only [h2, h7282, hlam]
                                        · linarith only [h7204, h7282, hlam]
                                  · linarith only [h3, h7277, hlam]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h0, hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h1, h5, h7215, hc13, hc34, hlam, hphi, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h5, hlam, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h6968, hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h1, hlam, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h4, hlam, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h7200, hlam, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h7202, hlam, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h2, hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h4, h7200, hc23, hc34, hlam, hphi, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  rcases p7221_3 (m.d 0 1) (by simp) with h7298 | h7298
                                  · rcases p7221_3 (m.d 0 2) (by simp) with h7299 | h7299
                                    · linarith only [h5, h7299, hlam]
                                    · linarith only [h4, h7299, hlam]
                                  · linarith only [h1, h7298, hlam]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h0, h5, h6968, h7205, h7215, hc23, hc34, hlam, hphi, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h3, hlam, p7221_0]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h0, h6968, h7205, h7215, h7219, hc23, hc34, hlam, hphi, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  rcases p7221_3 (m.d 0 1) (by simp) with h7307 | h7307
                                  · rcases p7221_3 (m.d 0 2) (by simp) with h7308 | h7308
                                    · linarith only [h6968, h7308, hlam]
                                    · linarith only [h4, h7308, hlam]
                                  · linarith only [h1, h7307, hlam]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [h7204, hlam, p7221_1]
                                · have p7221_0 := h7221c.1
                                  have p7221_1 := h7221c.2.1
                                  have p7221_2 := h7221c.2.2.1
                                  have p7221_3 := h7221c.2.2.2
                                  linarith only [hlam, p7221_0]
                              · linarith only [h0, h2, h5, h7205, h7214, h7215, h7220, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h2, h5, h7214, h7219, hlam]
                      · linarith only [h7200, h7204, h7205, h7206, h7214, hc23, hc34, hlam, hphi]
            · linarith only [h4, h6968, h7205, hc12, hc25, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7318 | h7318
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7319 | h7319
              · linarith only [h0, h5, h7319, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7321 | h7321
                · linarith only [h0, h6968, h7321, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7323 | h7323
                  · linarith only [h1, h7200, h7323, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7325 | h7325
                    · linarith only [h1, h7202, h7325, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7327 | h7327
                      · linarith only [h0, h2, h5, h7204, h7318, h7327, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7329 | h7329
                        · linarith only [h0, h1, h5, h7200, h7318, h7329, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7331 | h7331
                          · linarith only [h1, h7202, h7318, h7331, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7333 | h7333
                            · linarith only [h4, h5, h7204, h7329, h7333, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h5, h7318, h7333, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h7318, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  linarith only [h0, h4, h9253, hlam]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  linarith only [h0, h7337, h9255, hlam]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9257 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  linarith only [h0, h8360, h9257, hlam]

end R2N4
