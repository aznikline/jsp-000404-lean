import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h836 | h836
  · rcases m.htr 0 3 4 (by decide) (by decide) with h837 | h837
    · rcases m.htr 0 4 5 (by decide) (by decide) with h838 | h838
      · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
        · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
          · linarith only [h4, h836, h840, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h842 | h842
            · rcases m.htr 1 3 4 (by decide) (by decide) with h843 | h843
              · linarith only [h839, h840, h843, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h845 | h845
                · linarith only [h1, h837, h843, h845, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h847 | h847
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h848 | h848
                    · linarith only [h839, h845, h848, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h0, h1, h4, h837, h842, h848, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · linarith only [h840, h842, h847, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h4, h836, h842, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
          · linarith only [h4, h839, h853, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
            · rcases m.htr 1 3 4 (by decide) (by decide) with h856 | h856
              · rcases m.htr 1 3 5 (by decide) (by decide) with h857 | h857
                · rcases m.htr 1 4 5 (by decide) (by decide) with h858 | h858
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h859 | h859
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h860 | h860
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h861 | h861
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h862 | h862
                          · linarith only [h1, h856, h862, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases h1bigk with h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h839, h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h853, h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              rcases p864_3 (m.d 0 1) (by simp) with h869 | h869
                              · rcases p864_3 (m.d 1 2) (by simp) with h870 | h870
                                · linarith only [h0, h870, hlam]
                                · linarith only [h855, h870, hlam]
                              · linarith only [h869, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h0, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h839, hlam, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h853, hlam, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h0, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p864_1, u5ehi6]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h1, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h1, h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h1, h853, h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h1, h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h2, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h855, h861, h862, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h856, hlam, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h2, h855, h861, h862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p864_1]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h3, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h855, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h857, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [h858, hlam, p864_0]
                            · have p864_0 := h864c.1
                              have p864_1 := h864c.2.1
                              have p864_2 := h864c.2.2.1
                              have p864_3 := h864c.2.2.2
                              linarith only [hlam, p864_0]
                        · linarith only [h0, h4, h855, h861, hlam, hphi, u5ehi7, u5elo4]
                      · linarith only [h839, h855, h860, hlam, hphi, u5ehi7, u5elo3]
                    · linarith only [h839, h855, h859, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h838, h853, h855, h858, hlam, hphi, u5ehi7, u5elo0]
                · linarith only [h856, h857, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h1, h837, h839, h855, h856, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · linarith only [h4, h836, h855, hc12, hc24, hlam, hphi]
      · linarith only [h4, h836, h838, hlam, hphi, u5ehi7, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
      · rcases m.htr 1 2 3 (by decide) (by decide) with h903 | h903
        · rcases m.htr 1 2 4 (by decide) (by decide) with h904 | h904
          · linarith only [h0, h4, h836, h904, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h906 | h906
            · rcases m.htr 1 3 4 (by decide) (by decide) with h907 | h907
              · linarith only [h1, h837, h907, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
                · rcases m.htr 1 4 5 (by decide) (by decide) with h910 | h910
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h911 | h911
                    · linarith only [h1, h837, h909, h911, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h913 | h913
                      · linarith only [h0, h4, h903, h911, h913, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · linarith only [h1, h837, h909, h913, hc23, hc34, hlam, hphi]
                  · linarith only [h902, h903, h904, h910, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h917 | h917
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                    · linarith only [h0, h4, h837, h903, h918, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h920 | h920
                      · linarith only [h0, h4, h903, h918, h920, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h922 | h922
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h923 | h923
                          · rcases h1bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h906, h922, hc01, hlam, hphi, ht0b, ht5b, p924_1, u5ehi9]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              rcases p924_3 (m.d 0 1) (by simp) with h927 | h927
                              · rcases p924_3 (m.d 1 2) (by simp) with h928 | h928
                                · linarith only [h0, h928, hlam]
                                · linarith only [h903, h928, hlam]
                              · linarith only [h927, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h904, h906, h922, hc01, hlam, hphi, ht0b, ht5b, p924_1, u5ehi9]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              rcases p924_3 (m.d 0 1) (by simp) with h933 | h933
                              · rcases p924_3 (m.d 1 2) (by simp) with h934 | h934
                                · linarith only [h0, h934, hlam]
                                · linarith only [h906, h934, hlam]
                              · linarith only [h933, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, h4, h903, h918, hc23, hc34, hlam, hphi, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h904, hlam, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, h4, h918, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p924_1, u5ehi6]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h1, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h903, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h907, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h909, hlam, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h2, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h2, h903, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              rcases p924_3 (m.d 0 1) (by simp) with h950 | h950
                              · rcases p924_3 (m.d 1 2) (by simp) with h951 | h951
                                · linarith only [h904, h951, hlam]
                                · linarith only [h903, h951, hlam]
                              · linarith only [h1, h950, hlam]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h2, h906, h922, hc01, hlam, hphi, ht0b, ht5b, p924_1, u5ehi9]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h3, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h906, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, h4, h903, h906, h918, h922, hc23, hc34, hlam, hphi, p924_1, u5ehi9, u5elo1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h917, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                          · linarith only [h0, h4, h906, h918, h922, h923, hlam]
                        · linarith only [h0, h4, h906, h922, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                  · linarith only [h902, h904, h906, h917, hlam, hphi, u5ehi7, u5elo0]
            · linarith only [h4, h836, h906, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h966 | h966
          · linarith only [h4, h903, h966, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h968 | h968
            · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
              · linarith only [h1, h837, h969, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h971 | h971
                · rcases m.htr 1 4 5 (by decide) (by decide) with h972 | h972
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h973 | h973
                    · linarith only [h1, h837, h971, h973, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · linarith only [h903, h968, h973, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h902, h966, h968, h972, hlam, hphi, u5ehi7, u5elo0]
                · linarith only [h903, h968, h971, hlam, hphi, u5ehi7, u5elo3]
            · linarith only [h4, h836, h968, hc12, hc24, hlam, hphi]
      · linarith only [h4, h836, h902, hlam, hphi, u5ehi7, u5elo4]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h980 | h980
    · rcases m.htr 0 4 5 (by decide) (by decide) with h981 | h981
      · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
        · linarith only [h0, h836, h982, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h984 | h984
          · linarith only [h0, h836, h984, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h986 | h986
            · linarith only [h0, h836, h986, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h988 | h988
              · rcases m.htr 1 3 5 (by decide) (by decide) with h989 | h989
                · rcases m.htr 1 4 5 (by decide) (by decide) with h990 | h990
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h991 | h991
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h993 | h993
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h994 | h994
                          · linarith only [h1, h988, h994, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases h1bigk with h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              rcases p996_3 (m.d 0 1) (by simp) with h998 | h998
                              · rcases p996_3 (m.d 1 2) (by simp) with h999 | h999
                                · linarith only [h999, hlam, p996_0]
                                · rcases p996_3 (m.d 1 3) (by simp) with h1001 | h1001
                                  · linarith only [h1, h1001, hlam]
                                  · linarith only [h1001, h982, hlam]
                              · linarith only [h998, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h988, h990, h994, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h990, h994, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              rcases p996_3 (m.d 0 1) (by simp) with h1007 | h1007
                              · rcases p996_3 (m.d 1 2) (by simp) with h1008 | h1008
                                · linarith only [h0, h1008, hlam]
                                · rcases p996_3 (m.d 1 3) (by simp) with h1010 | h1010
                                  · linarith only [h1, h1010, hlam]
                                  · linarith only [h1010, h989, hlam]
                              · linarith only [h1007, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h0, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h982, hlam, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h984, hlam, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h986, hlam, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h1, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              rcases p996_3 (m.d 0 1) (by simp) with h1020 | h1020
                              · rcases p996_3 (m.d 1 2) (by simp) with h1021 | h1021
                                · linarith only [h1021, h982, hlam]
                                · rcases p996_3 (m.d 1 3) (by simp) with h1023 | h1023
                                  · rcases p996_3 (m.d 1 4) (by simp) with h1024 | h1024
                                    · linarith only [h1024, h988, hlam]
                                    · linarith only [h1024, h984, hlam]
                                  · linarith only [h1023, h982, hlam]
                              · linarith only [h0, h1020, hlam]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h1, h990, h994, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p996_1, u5ehi6]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h2, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              rcases p996_3 (m.d 0 1) (by simp) with h1033 | h1033
                              · rcases p996_3 (m.d 1 2) (by simp) with h1034 | h1034
                                · linarith only [h1034, h984, hlam]
                                · rcases p996_3 (m.d 1 3) (by simp) with h1036 | h1036
                                  · rcases p996_3 (m.d 1 4) (by simp) with h1037 | h1037
                                    · rcases p996_3 (m.d 1 5) (by simp) with h1038 | h1038
                                      · linarith only [h1038, h990, hlam]
                                      · linarith only [h1038, h986, hlam]
                                    · linarith only [h1037, h984, hlam]
                                  · linarith only [h1036, h982, hlam]
                              · linarith only [h0, h1033, hlam]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h988, hlam, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h2, h990, h994, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h3, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p996_1, u5elo1]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h989, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [h990, hlam, p996_0]
                            · have p996_0 := h996c.1
                              have p996_1 := h996c.2.1
                              have p996_2 := h996c.2.2.1
                              have p996_3 := h996c.2.2.2
                              linarith only [hlam, p996_0]
                        · linarith only [h4, h993, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h982, h992, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h982, h988, h991, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1055 | h1055
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1056 | h1056
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1057 | h1057
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1058 | h1058
                          · linarith only [h1058, h988, h990, hlam]
                          · rcases h1bigk with h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              rcases p1060_3 (m.d 0 1) (by simp) with h1062 | h1062
                              · rcases p1060_3 (m.d 1 2) (by simp) with h1063 | h1063
                                · linarith only [h1063, hlam, p1060_0]
                                · rcases p1060_3 (m.d 1 3) (by simp) with h1065 | h1065
                                  · linarith only [h1, h1065, hlam]
                                  · linarith only [h1065, h982, hlam]
                              · linarith only [h1062, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h989, hc01, hlam, hphi, ht0b, ht5b, p1060_1, u5ehi8]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              rcases p1060_3 (m.d 0 1) (by simp) with h1070 | h1070
                              · rcases p1060_3 (m.d 1 2) (by simp) with h1071 | h1071
                                · linarith only [h0, h1071, hlam]
                                · rcases p1060_3 (m.d 1 3) (by simp) with h1073 | h1073
                                  · linarith only [h1, h1073, hlam]
                                  · linarith only [h1073, h988, hlam]
                              · linarith only [h1070, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              rcases p1060_3 (m.d 0 1) (by simp) with h1077 | h1077
                              · rcases p1060_3 (m.d 1 2) (by simp) with h1078 | h1078
                                · linarith only [h0, h1078, hlam]
                                · rcases p1060_3 (m.d 1 3) (by simp) with h1080 | h1080
                                  · linarith only [h1, h1080, hlam]
                                  · linarith only [h1080, h989, hlam]
                              · linarith only [h1077, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h0, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h982, hlam, p1060_1]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h984, hlam, p1060_1]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h986, hlam, p1060_1]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h1, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              rcases p1060_3 (m.d 0 1) (by simp) with h1090 | h1090
                              · rcases p1060_3 (m.d 1 2) (by simp) with h1091 | h1091
                                · linarith only [h1091, h982, hlam]
                                · rcases p1060_3 (m.d 1 3) (by simp) with h1093 | h1093
                                  · rcases p1060_3 (m.d 1 4) (by simp) with h1094 | h1094
                                    · linarith only [h1094, h988, hlam]
                                    · linarith only [h1094, h984, hlam]
                                  · linarith only [h1093, h982, hlam]
                              · linarith only [h0, h1090, hlam]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              rcases p1060_3 (m.d 0 1) (by simp) with h1100 | h1100
                              · rcases p1060_3 (m.d 1 2) (by simp) with h1101 | h1101
                                · linarith only [h1101, h982, hlam]
                                · rcases p1060_3 (m.d 1 3) (by simp) with h1103 | h1103
                                  · rcases p1060_3 (m.d 1 4) (by simp) with h1104 | h1104
                                    · linarith only [h1104, h988, hlam]
                                    · rcases p1060_3 (m.d 1 5) (by simp) with h1106 | h1106
                                      · linarith only [h1106, h989, hlam]
                                      · linarith only [h1106, h990, hlam]
                                  · linarith only [h1103, h988, hlam]
                              · linarith only [h1100, h2, hlam]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p1060_1, u5ehi6]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h2, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h836, h981, h990, hc12, hlam, hphi, ht23, ht34, ht45, p1060_1, u5elo2]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h988, hlam, p1060_1]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h990, hlam, p1060_1]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h3, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1060_1, u5elo1]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h989, hlam, p1060_0]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [h836, h981, h990, hc14, hlam, hphi, ht45, p1060_1, u5elo2]
                            · have p1060_0 := h1060c.1
                              have p1060_1 := h1060c.2.1
                              have p1060_2 := h1060c.2.2.1
                              have p1060_3 := h1060c.2.2.2
                              linarith only [hlam, p1060_0]
                        · linarith only [h1057, h4, h981, hlam]
                      · linarith only [h1056, h982, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1055, h982, h988, hlam]
                · linarith only [h988, h989, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1126 | h1126
                · linarith only [h1126, h980, h988, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1129 | h1129
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1130 | h1130
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1131 | h1131
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1132 | h1132
                          · rcases h1bigk with h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              rcases p1133_3 (m.d 0 1) (by simp) with h1135 | h1135
                              · rcases p1133_3 (m.d 1 2) (by simp) with h1136 | h1136
                                · linarith only [h1136, hlam, p1133_0]
                                · rcases p1133_3 (m.d 1 3) (by simp) with h1138 | h1138
                                  · linarith only [h1, h1138, hlam]
                                  · linarith only [h1138, h982, hlam]
                              · linarith only [h1135, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              rcases p1133_3 (m.d 0 1) (by simp) with h1142 | h1142
                              · rcases p1133_3 (m.d 1 2) (by simp) with h1143 | h1143
                                · linarith only [h0, h1143, hlam]
                                · rcases p1133_3 (m.d 1 3) (by simp) with h1145 | h1145
                                  · linarith only [h1145, hlam, p1133_0]
                                  · rcases p1133_3 (m.d 1 4) (by simp) with h1147 | h1147
                                    · linarith only [h1147, h2, hlam]
                                    · linarith only [h1147, h988, hlam]
                              · linarith only [h1142, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1128, hc01, hlam, hphi, ht0b, ht5b, p1133_1, u5ehi9]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              rcases p1133_3 (m.d 0 1) (by simp) with h1152 | h1152
                              · rcases p1133_3 (m.d 1 2) (by simp) with h1153 | h1153
                                · linarith only [h0, h1153, hlam]
                                · rcases p1133_3 (m.d 1 3) (by simp) with h1155 | h1155
                                  · linarith only [h1, h1155, hlam]
                                  · rcases p1133_3 (m.d 1 4) (by simp) with h1157 | h1157
                                    · linarith only [h1157, h2, hlam]
                                    · linarith only [h1128, h1157, hlam]
                              · linarith only [h1152, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h0, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h982, hlam, p1133_1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h984, hlam, p1133_1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h986, hlam, p1133_1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1126, h1130, hc12, hlam, hphi, ht23, ht34, ht45, p1133_1, u5elo2]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h988, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1126, hlam, p1133_1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h2, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1129, h988, hc12, hc23, hlam, hphi, p1133_1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1129, h982, h988, hc12, hc23, hlam, hphi, p1133_1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1129, h988, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1133_1, u5ehi6]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h3, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1133_1, u5elo1]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h3, h836, h982, hc12, hlam, hphi, ht23, ht34, ht45, p1133_1, u5elo2]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [h1128, hlam, p1133_0]
                            · have p1133_0 := h1133c.1
                              have p1133_1 := h1133c.2.1
                              have p1133_2 := h1133c.2.2.1
                              have p1133_3 := h1133c.2.2.2
                              linarith only [hlam, p1133_0]
                          · linarith only [h1132, h836, h981, h982, h988, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1128, h1131, h4, h980, h988, hlam]
                      · linarith only [h1128, h1129, h1130, h988, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h1129, h4, h980, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1185 | h1185
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1186 | h1186
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1187 | h1187
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1188 | h1188
                          · linarith only [h1128, h1185, h1188, h984, hc12, hc23, hlam, hphi]
                          · linarith only [h1188, h4, h981, h982, h988, hc12, hc24, hlam, hphi]
                        · linarith only [h1187, h4, h981, hlam]
                      · linarith only [h1186, h982, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1185, h4, h980, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1194 | h1194
        · linarith only [h0, h1194, h4, h981, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1196 | h1196
          · linarith only [h0, h1196, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
            · linarith only [h0, h1198, h4, h836, h981, hlam, hphi, u5ehi5, u5elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1200 | h1200
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1201 | h1201
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1202 | h1202
                  · linarith only [h1202, h2, h981, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1204 | h1204
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1207 | h1207
                          · linarith only [h1207, h980, h981, hlam]
                          · rcases h1bigk with h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              rcases p1209_3 (m.d 0 1) (by simp) with h1211 | h1211
                              · rcases p1209_3 (m.d 1 2) (by simp) with h1212 | h1212
                                · linarith only [h1212, hlam, p1209_0]
                                · rcases p1209_3 (m.d 1 3) (by simp) with h1214 | h1214
                                  · linarith only [h1, h1214, hlam]
                                  · linarith only [h1194, h1214, hlam]
                              · linarith only [h1211, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1201, hc01, hlam, hphi, ht0b, ht5b, p1209_1, u5ehi8]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              rcases p1209_3 (m.d 0 1) (by simp) with h1219 | h1219
                              · rcases p1209_3 (m.d 1 2) (by simp) with h1220 | h1220
                                · linarith only [h0, h1220, hlam]
                                · rcases p1209_3 (m.d 1 3) (by simp) with h1222 | h1222
                                  · linarith only [h1, h1222, hlam]
                                  · linarith only [h1200, h1222, hlam]
                              · linarith only [h1219, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              rcases p1209_3 (m.d 0 1) (by simp) with h1226 | h1226
                              · rcases p1209_3 (m.d 1 2) (by simp) with h1227 | h1227
                                · linarith only [h0, h1227, hlam]
                                · rcases p1209_3 (m.d 1 3) (by simp) with h1229 | h1229
                                  · linarith only [h1, h1229, hlam]
                                  · linarith only [h1201, h1229, hlam]
                              · linarith only [h1226, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h0, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1194, hlam, p1209_1]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1196, hlam, p1209_1]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1198, hlam, p1209_1]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              rcases p1209_3 (m.d 0 1) (by simp) with h1239 | h1239
                              · rcases p1209_3 (m.d 1 2) (by simp) with h1240 | h1240
                                · linarith only [h1194, h1240, hlam]
                                · rcases p1209_3 (m.d 1 3) (by simp) with h1242 | h1242
                                  · rcases p1209_3 (m.d 1 4) (by simp) with h1243 | h1243
                                    · linarith only [h1200, h1243, hlam]
                                    · linarith only [h1196, h1243, hlam]
                                  · linarith only [h1194, h1242, hlam]
                              · linarith only [h0, h1239, hlam]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              rcases p1209_3 (m.d 0 1) (by simp) with h1249 | h1249
                              · rcases p1209_3 (m.d 1 2) (by simp) with h1250 | h1250
                                · linarith only [h1194, h1250, hlam]
                                · rcases p1209_3 (m.d 1 3) (by simp) with h1252 | h1252
                                  · rcases p1209_3 (m.d 1 4) (by simp) with h1253 | h1253
                                    · linarith only [h1200, h1253, hlam]
                                    · rcases p1209_3 (m.d 1 5) (by simp) with h1255 | h1255
                                      · linarith only [h1201, h1255, hlam]
                                      · linarith only [h1202, h1255, hlam]
                                  · linarith only [h1200, h1252, hlam]
                              · linarith only [h1249, h2, hlam]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1, h1201, hc01, hlam, hphi, ht0b, ht5b, p1209_1, u5ehi8]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h2, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1206, h2, h981, hc12, hlam, hphi, ht23, ht34, ht45, p1209_1, u5elo2]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1200, hlam, p1209_1]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1202, hlam, p1209_1]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h3, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht23, ht34, ht45, p1209_1, u5elo0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1201, hlam, p1209_0]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [h1206, h3, h981, hc14, hlam, hphi, ht45, p1209_1, u5elo2]
                            · have p1209_0 := h1209c.1
                              have p1209_1 := h1209c.2.1
                              have p1209_2 := h1209c.2.2.1
                              have p1209_3 := h1209c.2.2.2
                              linarith only [hlam, p1209_0]
                        · linarith only [h1206, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1194, h1205, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1, h1194, h1201, h1204, h980, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · linarith only [h1200, h1201, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h1200, h980, h981, hc13, hlam, hphi, ht34, ht45, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1276 | h1276
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1277 | h1277
        · linarith only [h0, h1277, h836, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1279 | h1279
          · linarith only [h0, h1276, h1279, h4, h836, hlam, hphi, u5ehi9, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1281 | h1281
            · linarith only [h0, h1281, h836, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1283 | h1283
              · linarith only [h1, h1283, h980, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1285 | h1285
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1286 | h1286
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1287 | h1287
                    · linarith only [h1, h1285, h1287, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1289 | h1289
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1290 | h1290
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1291 | h1291
                          · rcases h1bigk with h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              rcases p1292_3 (m.d 0 1) (by simp) with h1294 | h1294
                              · rcases p1292_3 (m.d 1 2) (by simp) with h1295 | h1295
                                · linarith only [h1295, hlam, p1292_0]
                                · rcases p1292_3 (m.d 1 3) (by simp) with h1297 | h1297
                                  · linarith only [h1, h1297, hlam]
                                  · linarith only [h1277, h1297, hlam]
                              · linarith only [h1294, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1285, h1291, hc01, hlam, hphi, ht0b, ht5b, p1292_1, u5ehi9]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1283, h1285, h1291, hc01, hlam, hphi, ht0b, ht5b, p1292_1, u5ehi9]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              rcases p1292_3 (m.d 0 1) (by simp) with h1303 | h1303
                              · rcases p1292_3 (m.d 1 2) (by simp) with h1304 | h1304
                                · linarith only [h0, h1304, hlam]
                                · rcases p1292_3 (m.d 1 3) (by simp) with h1306 | h1306
                                  · linarith only [h1, h1306, hlam]
                                  · linarith only [h1285, h1306, hlam]
                              · linarith only [h1303, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h0, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1277, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1279, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1281, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1, h980, hc12, hc34, hlam, hphi, ht23, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1283, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1292_1, u5ehi6]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h2, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              rcases p1292_3 (m.d 0 1) (by simp) with h1321 | h1321
                              · rcases p1292_3 (m.d 1 2) (by simp) with h1322 | h1322
                                · linarith only [h1279, h1322, hlam]
                                · rcases p1292_3 (m.d 1 3) (by simp) with h1324 | h1324
                                  · linarith only [h1283, h1324, hlam]
                                  · linarith only [h1277, h1324, hlam]
                              · linarith only [h0, h1321, hlam]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1285, h2, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1292_1, u5ehi8]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1285, h1291, h2, hc01, hlam, hphi, ht0b, ht5b, p1292_1, u5ehi9]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h3, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1, h1285, h1291, h980, hc12, hc34, hlam, hphi, ht23, p1292_1, u5ehi9, u5elo1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1285, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1286, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                          · linarith only [h1, h1285, h1291, h980, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                        · linarith only [h1286, h1290, h3, h4, h836, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1, h1285, h1289, h980, hc23, hc34, hlam, hphi]
                  · linarith only [h1276, h1283, h1285, h1286, h836, hlam, hphi, u5ehi8, u5elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1340 | h1340
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1341 | h1341
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1342 | h1342
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1343 | h1343
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1344 | h1344
                          · rcases h1bigk with h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              rcases p1345_3 (m.d 0 1) (by simp) with h1347 | h1347
                              · rcases p1345_3 (m.d 1 2) (by simp) with h1348 | h1348
                                · linarith only [h1348, hlam, p1345_0]
                                · rcases p1345_3 (m.d 1 3) (by simp) with h1350 | h1350
                                  · linarith only [h1, h1350, hlam]
                                  · linarith only [h1277, h1350, hlam]
                              · linarith only [h1347, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              rcases p1345_3 (m.d 0 1) (by simp) with h1354 | h1354
                              · rcases p1345_3 (m.d 1 2) (by simp) with h1355 | h1355
                                · linarith only [h0, h1355, hlam]
                                · rcases p1345_3 (m.d 1 3) (by simp) with h1357 | h1357
                                  · linarith only [h1357, hlam, p1345_0]
                                  · rcases p1345_3 (m.d 1 4) (by simp) with h1359 | h1359
                                    · linarith only [h1359, h2, hlam]
                                    · linarith only [h1283, h1359, hlam]
                              · linarith only [h1354, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1340, hc01, hlam, hphi, ht0b, ht5b, p1345_1, u5ehi9]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              rcases p1345_3 (m.d 0 1) (by simp) with h1364 | h1364
                              · rcases p1345_3 (m.d 1 2) (by simp) with h1365 | h1365
                                · linarith only [h0, h1365, hlam]
                                · rcases p1345_3 (m.d 1 3) (by simp) with h1367 | h1367
                                  · linarith only [h1, h1367, hlam]
                                  · rcases p1345_3 (m.d 1 4) (by simp) with h1369 | h1369
                                    · linarith only [h1369, h2, hlam]
                                    · linarith only [h1340, h1369, hlam]
                              · linarith only [h1364, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h0, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1277, hlam, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1279, hlam, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1281, hlam, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1, h1341, h980, hc12, hc23, hlam, hphi, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1283, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1285, hlam, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h2, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1341, h2, h980, hc12, hc23, hlam, hphi, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1277, h1341, h2, h980, hc12, hc23, hlam, hphi, p1345_1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1341, h2, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1345_1, u5ehi6]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h3, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1345_1, u5elo1]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1277, h3, h836, hc12, hlam, hphi, ht23, ht34, ht45, p1345_1, u5elo2]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [h1340, hlam, p1345_0]
                            · have p1345_0 := h1345c.1
                              have p1345_1 := h1345c.2.1
                              have p1345_2 := h1345c.2.2.1
                              have p1345_3 := h1345c.2.2.2
                              linarith only [hlam, p1345_0]
                          · linarith only [h1344, h980, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1340, h1341, h1343, h2, h980, hlam]
                      · linarith only [h1277, h1342, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1396 | h1396
                      · linarith only [h1277, h1285, h1341, h1396, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1277, h1396, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1399 | h1399
                    · linarith only [h1276, h1277, h1283, h1340, h1399, h980, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1401 | h1401
                      · linarith only [h1277, h1285, h1399, h1401, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1277, h1401, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1404 | h1404
        · linarith only [h0, h1276, h1404, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1406 | h1406
          · linarith only [h1404, h1406, h4, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1408 | h1408
            · linarith only [h0, h1276, h1408, h3, h4, h836, hlam, hphi, u5ehi6, u5elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1410 | h1410
              · linarith only [h1, h1276, h1410, h980, hc34, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1412 | h1412
                · linarith only [h1, h1276, h1412, h980, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
                  · linarith only [h1276, h1414, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1416 | h1416
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1417 | h1417
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1418 | h1418
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1419 | h1419
                          · linarith only [h1276, h1416, h1419, h4, hc02, hc23, hlam, hphi]
                          · linarith only [h1, h1404, h1419, h980, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1418, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1404, h1417, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1424 | h1424
                      · linarith only [h1404, h1412, h1416, h1424, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1404, h1424, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
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

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
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
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1428 | h1428
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1429 | h1429
    · linarith only [h0, h1429, h2, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1431 | h1431
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1432 | h1432
        · linarith only [h1, h1432, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1434 | h1434
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1435 | h1435
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1436 | h1436
              · linarith only [h0, h1429, h1431, h1436, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1438 | h1438
                · linarith only [h0, h1436, h1438, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                · linarith only [h1435, h1438, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1441 | h1441
              · linarith only [h1429, h1435, h1441, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1443 | h1443
                · linarith only [h0, h1441, h1443, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                · linarith only [h0, h1431, h1441, h1443, h2, hc12, hc24, hlam, hphi]
          · linarith only [h1, h1434, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1447 | h1447
        · linarith only [h1, h1447, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1449 | h1449
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1450 | h1450
            · linarith only [h0, h1431, h1450, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1452 | h1452
              · linarith only [h0, h1431, h1452, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1454 | h1454
                · linarith only [h0, h1431, h1454, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1456 | h1456
                  · linarith only [h1, h1447, h1456, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1458 | h1458
                    · linarith only [h1, h1456, h1458, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1460 | h1460
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1461 | h1461
                        · linarith only [h0, h1456, h1461, h2, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1463 | h1463
                          · linarith only [h1458, h1461, h1463, hc13, hc34, hlam, hphi]
                          · linarith only [h1450, h1463, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1428, h1460, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
          · linarith only [h1428, h1449, h2, hlam, hphi, u5ehi6, u5elo4]
  · linarith only [h0, h1428, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
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
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1469 | h1469
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1470 | h1470
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1471 | h1471
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1472 | h1472
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1473 | h1473
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1474 | h1474
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1475 | h1475
              · linarith only [h0, h1, h1475, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1477 | h1477
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1478 | h1478
                  · linarith only [h0, h1, h1478, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h0, h1, h1472, h1475, h1478, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h1471, h1475, h1477, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1482 | h1482
              · linarith only [h0, h1, h1482, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1484 | h1484
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
                  · linarith only [h0, h1, h1485, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h0, h1, h1472, h1482, h1485, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h1471, h1482, h1484, hc12, hc23, hlam, hphi]
          · linarith only [h1, h1469, h1473, hlam]
        · linarith only [h1471, h1472, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1491 | h1491
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1492 | h1492
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1493 | h1493
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1494 | h1494
              · linarith only [h0, h1, h1494, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1496 | h1496
                · linarith only [h0, h1471, h1491, h1496, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1498 | h1498
                  · linarith only [h1, h1469, h1494, h1496, h1498, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                  · linarith only [h1471, h1491, h1498, hc12, hc24, hlam, hphi]
            · linarith only [h1471, h1491, h1493, hlam, hphi, u5ehi7, u5elo4]
          · linarith only [h1, h1469, h1492, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1503 | h1503
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1504 | h1504
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1505 | h1505
              · linarith only [h0, h1491, h1505, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1507 | h1507
                · linarith only [h0, h1471, h1491, h1507, hc04, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1509 | h1509
                  · linarith only [h0, h1491, h1509, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1512 | h1512
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1513 | h1513
                        · linarith only [h1, h1469, h1505, h1513, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                        · linarith only [h1, h1469, h1504, h1505, h1507, h1513, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h1469, h1504, h1512, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h1, h1469, h1504, h1511, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1518 | h1518
              · linarith only [h0, h1471, h1504, h1518, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1520 | h1520
                · linarith only [h0, h1471, h1520, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1522 | h1522
                  · linarith only [h0, h1471, h1504, h1522, hlam, hphi, u5ehi7, u5elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1524 | h1524
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1525 | h1525
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1526 | h1526
                        · linarith only [h1469, h1504, h1526, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1528 | h1528
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1529 | h1529
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1530 | h1530
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1531 | h1531
                                · linarith only [h1469, h1504, h1524, h1531, hlam]
                                · rcases h1bigk with h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1, h1518, hc12, hc23, hlam, hphi, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1, h1518, h1520, hc12, hc23, hlam, hphi, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1, h1518, h1525, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1533_1, u5ehi8]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1518, hlam, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1520, hlam, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1522, hlam, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, h1518, hc12, hc23, hlam, hphi, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    rcases p1533_3 (m.d 0 1) (by simp) with h1545 | h1545
                                    · linarith only [h1, h1545, hlam]
                                    · linarith only [h0, h1545, hlam]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    rcases p1533_3 (m.d 0 1) (by simp) with h1549 | h1549
                                    · linarith only [h1, h1549, hlam]
                                    · linarith only [h1469, h1549, hlam]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    rcases p1533_3 (m.d 0 1) (by simp) with h1552 | h1552
                                    · linarith only [h1, h1552, hlam]
                                    · linarith only [h1470, h1552, hlam]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1469, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1, h1469, h1518, hc12, hc23, hlam, hphi, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1524, hlam, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1526, hlam, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1470, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1533_1, u5elo1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1525, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1, h1470, h1518, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                              · linarith only [h0, h1471, h1530, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h1, h1470, h1518, h1529, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                          · linarith only [h1, h1470, h1518, h1525, h1528, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · linarith only [h1, h1470, h1525, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                    · linarith only [h1, h1470, h1503, h1524, hc04, hlam, hphi, ht0b, ht5b, u5ehi6]
          · linarith only [h1, h1469, h1503, hlam]
    · linarith only [h0, h1470, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1572 | h1572
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1573 | h1573
      · linarith only [h0, h1469, h1573, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1575 | h1575
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1576 | h1576
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1577 | h1577
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1578 | h1578
              · linarith only [h0, h1, h1578, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1580 | h1580
                · linarith only [h0, h1573, h1575, h1580, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1582 | h1582
                  · linarith only [h0, h1, h1578, h1582, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                  · linarith only [h0, h1, h1575, h1578, h1582, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1469, h1575, h1577, hlam, hphi, u5ehi7, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1586 | h1586
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
              · linarith only [h0, h1, h1576, h1587, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1589 | h1589
                · linarith only [h0, h1, h1573, h1575, h1576, h1589, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1591 | h1591
                  · linarith only [h0, h1, h1576, h1591, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h0, h1, h1575, h1576, h1591, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h1, h1575, h1576, h1586, hlam, hphi, u5ehi7, u5elo4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1595 | h1595
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1596 | h1596
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1597 | h1597
              · linarith only [h0, h1575, h1597, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1599 | h1599
                · linarith only [h0, h1575, h1599, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1601 | h1601
                  · linarith only [h0, h1575, h1601, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1603 | h1603
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1604 | h1604
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1605 | h1605
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1606 | h1606
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1607 | h1607
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1608 | h1608
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1609 | h1609
                                · rcases h1bigk with h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1469, h1597, h1603, hc12, hc23, hlam, hphi, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1469, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1469, h1597, h1603, h1604, h1609, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1610_1, u5ehi9]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h0, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1597, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1599, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1601, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h0, h1597, hc12, hc23, hlam, hphi, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1622 | h1622
                                    · linarith only [h1, h1622, hlam]
                                    · linarith only [h0, h1622, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1469, h1572, h1597, h1604, h1609, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1610_1, u5ehi9]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1627 | h1627
                                    · linarith only [h1, h1627, hlam]
                                    · linarith only [h1572, h1627, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1572, h1604, h1609, hc14, hlam, hphi, ht01, ht0b, ht5b, p1610_1, u5ehi9]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1631 | h1631
                                    · linarith only [h1469, h1631, hlam]
                                    · linarith only [h0, h1631, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1603, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1636 | h1636
                                    · linarith only [h1469, h1636, hlam]
                                    · linarith only [h1572, h1636, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1572, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1610_1, u5elo1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1604, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1605, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                · rcases h1bigk with h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c | h1644c
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1469, h1597, h1603, hc12, hc23, hlam, hphi, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1, hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1469, hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1469, h1597, h1603, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1644_1, u5ehi6]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h0, hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1597, hlam, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1599, hlam, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1601, hlam, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h0, h1597, hc12, hc23, hlam, hphi, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    rcases p1644_3 (m.d 0 1) (by simp) with h1656 | h1656
                                    · linarith only [h1, h1656, hlam]
                                    · linarith only [h0, h1656, hlam]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1469, h1572, h1597, h1605, h1609, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    rcases p1644_3 (m.d 0 1) (by simp) with h1661 | h1661
                                    · linarith only [h1, h1661, hlam]
                                    · linarith only [h1572, h1661, hlam]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1572, h1605, h1609, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    rcases p1644_3 (m.d 0 1) (by simp) with h1665 | h1665
                                    · linarith only [h1469, h1665, hlam]
                                    · linarith only [h0, h1665, hlam]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1603, hlam, p1644_1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    rcases p1644_3 (m.d 0 1) (by simp) with h1670 | h1670
                                    · linarith only [h1469, h1670, hlam]
                                    · linarith only [h1572, h1670, hlam]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1572, hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1644_1, u5elo1]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1604, hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [h1605, hlam, p1644_0]
                                  · have p1644_0 := h1644c.1
                                    have p1644_1 := h1644c.2.1
                                    have p1644_2 := h1644c.2.2.1
                                    have p1644_3 := h1644c.2.2.2
                                    linarith only [hlam, p1644_0]
                              · linarith only [h1469, h1572, h1599, h1605, h1608, hlam]
                            · linarith only [h1469, h1572, h1599, h1604, h1606, h1607, hlam]
                          · linarith only [h1, h1572, h1597, h1604, h1606, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h1469, h1572, h1605, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
                      · linarith only [h1469, h1572, h1603, h1604, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                    · linarith only [h1, h1595, h1603, hlam]
            · linarith only [h1469, h1572, h1596, hlam, hphi, u5ehi6, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1685 | h1685
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1686 | h1686
              · linarith only [h0, h1575, h1686, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1688 | h1688
                · linarith only [h0, h1575, h1688, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1690 | h1690
                  · linarith only [h0, h1575, h1690, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1692 | h1692
                    · linarith only [h1, h1572, h1595, h1692, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                    · linarith only [h1, h1572, h1692, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
            · linarith only [h1, h1572, h1595, h1685, hlam, hphi, u5ehi6, u5elo4]
    · linarith only [h0, h1572, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

end R2N4
