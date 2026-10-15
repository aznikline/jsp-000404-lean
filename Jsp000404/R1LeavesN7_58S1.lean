import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h823 | h823
  · rcases m.htr 0 2 5 (by decide) (by decide) with h824 | h824
    · linarith only [h3, h824, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h826 | h826
      · rcases m.htr 0 3 5 (by decide) (by decide) with h827 | h827
        · rcases m.htr 0 4 5 (by decide) (by decide) with h828 | h828
          · linarith only [h3, h823, h828, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
            · linarith only [h3, h830, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h832 | h832
              · rcases m.htr 1 2 5 (by decide) (by decide) with h833 | h833
                · linarith only [h0, h824, h833, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h835 | h835
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h836 | h836
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h837 | h837
                      · linarith only [h0, h3, h828, h832, h837, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h841 | h841
                            · linarith only [h823, h824, h837, h840, h841, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                              · linarith only [h0, h824, h826, h832, h841, h843, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0emin with h845 | h845 | h845 | h845 | h845
                                · rcases h3bigk with h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h3, h836, hlam, hphi, ht01, ht0b, ht12, ht5b, p846_1, u2elo2, u5ehi3]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h3, hlam, p846_1]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    rcases p846_3 (m.d 0 3) (by simp) with h850 | h850
                                    · rcases p846_3 (m.d 1 3) (by simp) with h851 | h851
                                      · linarith only [h1, h851, hlam]
                                      · linarith only [h835, h851, hlam]
                                    · linarith only [h850, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p846_1, u2elo2, u5ehi3]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h1, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h830, hlam, p846_1]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    rcases p846_3 (m.d 0 3) (by simp) with h859 | h859
                                    · rcases p846_3 (m.d 1 3) (by simp) with h860 | h860
                                      · rcases p846_3 (m.d 2 3) (by simp) with h861 | h861
                                        · rcases p846_3 (m.d 3 4) (by simp) with h862 | h862
                                          · linarith only [h862, hlam, p846_0]
                                          · rcases p846_3 (m.d 3 5) (by simp) with h864 | h864
                                            · linarith only [h836, h864, hlam]
                                            · linarith only [h843, h864, hlam]
                                        · linarith only [h839, h861, hlam]
                                      · linarith only [h860, hlam, p846_0]
                                    · linarith only [h826, h859, hlam]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p846_1, u5ehi3]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h0, h3, h832, h839, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p846_1, u2elo2]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h830, h832, h839, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p846_1, u2elo2]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    rcases p846_3 (m.d 0 3) (by simp) with h874 | h874
                                    · linarith only [h3, h874, hlam]
                                    · linarith only [h826, h874, hlam]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p846_1, u2elo2, u5ehi3]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h826, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h835, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h839, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h843, hlam, p846_1]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h827, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h836, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h840, hlam, p846_0]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [h1, h836, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p846_1]
                                  · have p846_0 := h846c.1
                                    have p846_1 := h846c.2.1
                                    have p846_2 := h846c.2.2.1
                                    have p846_3 := h846c.2.2.2
                                    linarith only [hlam, p846_0]
                                · linarith only [h824, h845, hlam, ht01, ht12, u2elo4]
                                · linarith only [h3, h845, hlam, ht01, ht12, u2elo2]
                                · linarith only [h823, h824, h845, hlam, ht01, ht12, u2elo4]
                                · linarith only [h824, h845, hlam, ht01, ht12, u2elo4]
                          · linarith only [h1, h3, h836, h840, hlam]
                        · linarith only [h3, h826, h839, hlam]
                    · linarith only [h3, h827, h830, h832, h836, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h3, h826, h830, h832, h835, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h3, h823, h832, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h897 | h897
          · linarith only [h3, h823, h897, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h899 | h899
            · linarith only [h3, h899, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h901 | h901
              · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                · linarith only [h1, h824, h827, h899, h902, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h905 | h905
                    · linarith only [h1, h827, h905, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h907 | h907
                      · linarith only [h0, h3, h897, h901, h907, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h909 | h909
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h910 | h910
                          · linarith only [h1, h827, h899, h910, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h912 | h912
                            · linarith only [h901, h907, h912, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h914 | h914
                              · linarith only [h0, h3, h826, h827, h901, h910, h912, h914, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h3, h901, h909, h910, h914, hc34, hc45, hlam, hphi]
                        · linarith only [h3, h826, h909, hlam]
                  · linarith only [h3, h823, h826, h899, h901, h904, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h3, h823, h901, hc12, hlam, hphi, u2elo2]
      · linarith only [h3, h823, h826, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h921 | h921
    · linarith only [h3, h921, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h923 | h923
      · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
        · rcases m.htr 0 4 5 (by decide) (by decide) with h925 | h925
          · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
            · linarith only [h3, h926, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h928 | h928
              · linarith only [h0, h823, h925, h928, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h930 | h930
                · linarith only [h0, h921, h930, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h933 | h933
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h935 | h935
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h936 | h936
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h937 | h937
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h938 | h938
                              · linarith only [h1, h932, h938, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h0emin with h940 | h940 | h940 | h940 | h940
                                · rcases h3bigk with h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c | h941c
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h3, h926, hc12, hlam, hphi, p941_1, u2elo2]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h3, hlam, p941_1]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    rcases p941_3 (m.d 0 3) (by simp) with h945 | h945
                                    · rcases p941_3 (m.d 1 3) (by simp) with h946 | h946
                                      · linarith only [h1, h946, hlam]
                                      · linarith only [h932, h946, hlam]
                                    · linarith only [h945, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p941_1, u2elo2, u5ehi3]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h1, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h926, hlam, p941_1]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    rcases p941_3 (m.d 0 3) (by simp) with h954 | h954
                                    · rcases p941_3 (m.d 1 3) (by simp) with h955 | h955
                                      · rcases p941_3 (m.d 2 3) (by simp) with h956 | h956
                                        · rcases p941_3 (m.d 3 4) (by simp) with h957 | h957
                                          · linarith only [h957, hlam, p941_0]
                                          · rcases p941_3 (m.d 3 5) (by simp) with h959 | h959
                                            · linarith only [h933, h959, hlam]
                                            · linarith only [h938, h959, hlam]
                                        · linarith only [h935, h956, hlam]
                                      · linarith only [h955, hlam, p941_0]
                                    · linarith only [h923, h954, hlam]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p941_1, u5ehi3]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h3, hc02, hlam, hphi, p941_1, u2elo2]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h926, hc12, hlam, hphi, p941_1, u2elo2]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    rcases p941_3 (m.d 0 3) (by simp) with h969 | h969
                                    · linarith only [h3, h969, hlam]
                                    · linarith only [h923, h969, hlam]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p941_1, u2elo2, u5ehi3]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h923, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h932, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h935, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h938, hlam, p941_1]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h924, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h933, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h936, hlam, p941_0]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [h3, h924, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p941_1, u2elo2]
                                  · have p941_0 := h941c.1
                                    have p941_1 := h941c.2.1
                                    have p941_2 := h941c.2.2.1
                                    have p941_3 := h941c.2.2.2
                                    linarith only [hlam, p941_0]
                                · linarith only [h940, hlam, ht01, ht12, u2elo0]
                                · linarith only [h3, h940, hlam, ht01, ht12, u2elo2]
                                · linarith only [h823, h935, h940, hlam, ht01, ht12, u2elo2]
                                · linarith only [h823, h925, h935, h940, hlam, ht01, ht12, u2elo2]
                            · linarith only [h1, h823, h932, h934, h937, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h2, h3, h932, h933, h934, h936, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h3, h923, h935, hlam]
                      · linarith only [h3, h923, h925, h928, h934, hc12, hlam, hphi, u2elo2]
                    · linarith only [h3, h924, h932, h933, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h3, h923, h926, h932, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h993 | h993
            · linarith only [h3, h924, h993, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h995 | h995
              · linarith only [h0, h823, h995, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h997 | h997
                · linarith only [h0, h921, h997, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h999 | h999
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1000 | h1000
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1001 | h1001
                      · linarith only [h1001, h823, h925, h995, hc02, hlam, hphi, u2elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1003 | h1003
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1004 | h1004
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1005 | h1005
                            · linarith only [h0, h1003, h1005, h823, h925, hc12, hlam, hphi, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1007 | h1007
                              · linarith only [h1007, h3, h923, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                              · rcases h0emin with h1009 | h1009 | h1009 | h1009 | h1009
                                · rcases h3bigk with h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1000, h1007, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1010_1, u2elo2]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h3, hlam, p1010_1]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    rcases p1010_3 (m.d 0 3) (by simp) with h1014 | h1014
                                    · rcases p1010_3 (m.d 1 3) (by simp) with h1015 | h1015
                                      · linarith only [h1, h1015, hlam]
                                      · linarith only [h1015, h999, hlam]
                                    · linarith only [h1014, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p1010_1, u2elo2, u5ehi3]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h993, hlam, p1010_1]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    rcases p1010_3 (m.d 0 3) (by simp) with h1023 | h1023
                                    · rcases p1010_3 (m.d 1 3) (by simp) with h1024 | h1024
                                      · rcases p1010_3 (m.d 2 3) (by simp) with h1025 | h1025
                                        · rcases p1010_3 (m.d 3 4) (by simp) with h1026 | h1026
                                          · linarith only [h1026, hlam, p1010_0]
                                          · rcases p1010_3 (m.d 3 5) (by simp) with h1028 | h1028
                                            · linarith only [h1000, h1028, hlam]
                                            · linarith only [h1007, h1028, hlam]
                                        · linarith only [h1003, h1025, hlam]
                                      · linarith only [h1024, hlam, p1010_0]
                                    · linarith only [h1023, h923, hlam]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p1010_1, u5ehi3]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h924, hlam, hphi, ht01, ht0b, ht12, ht5b, p1010_1, u2elo2, u5ehi0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h993, hc12, hlam, hphi, p1010_1, u2elo2]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    rcases p1010_3 (m.d 0 3) (by simp) with h1038 | h1038
                                    · linarith only [h1038, h3, hlam]
                                    · linarith only [h1038, h923, hlam]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p1010_1, u2elo2, u5ehi3]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h923, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h999, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1003, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1007, hlam, p1010_1]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h924, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1000, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1004, hlam, p1010_0]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [h1, h1000, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1010_1]
                                  · have p1010_0 := h1010c.1
                                    have p1010_1 := h1010c.2.1
                                    have p1010_2 := h1010c.2.2.1
                                    have p1010_3 := h1010c.2.2.2
                                    linarith only [hlam, p1010_0]
                                · linarith only [h1009, hlam, ht01, ht12, u2elo0]
                                · linarith only [h1009, h3, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1005, h1009, h823, hc45, hlam, ht01, ht12, ht23, ht34]
                                · linarith only [h1004, h1009, h921, hlam, ht01, ht12, u2elo2]
                          · linarith only [h1, h1000, h1004, h3, hlam]
                        · linarith only [h1003, h3, h923, hlam]
                    · linarith only [h1000, h3, h924, h999, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h3, h923, h993, h999, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1060 | h1060
          · linarith only [h1060, h923, h924, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1062 | h1062
            · linarith only [h1062, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1064 | h1064
              · linarith only [h0, h1064, h823, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1066 | h1066
                · linarith only [h0, h1066, h823, h921, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1068 | h1068
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1069 | h1069
                    · linarith only [h1, h1069, h924, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1071 | h1071
                      · linarith only [h1, h1060, h1068, h1071, h823, h924, hc02, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1073 | h1073
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1074 | h1074
                          · linarith only [h0, h1074, h3, h924, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1076 | h1076
                            · linarith only [h0, h1060, h1076, h823, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1078 | h1078
                              · linarith only [h1, h1068, h1076, h1078, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0emin with h1080 | h1080 | h1080 | h1080 | h1080
                                · rcases h3bigk with h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1074, h1078, h3, hc13, hc45, hlam, hphi, ht34, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h3, hlam, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1074, h1078, h3, hc34, hc45, hlam, hphi, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h924, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1062, hlam, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1, h1074, h1078, h3, hc34, hc45, hlam, hphi, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1069, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1074, h1078, hc03, hc45, hlam, hphi, ht34, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1074, h1078, hc13, hc45, hlam, hphi, ht34, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1074, h1078, hc34, hc45, hlam, hphi, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1074, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h923, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1068, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1073, hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1078, hlam, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1, h1068, h1078, hc34, hc45, hlam, hphi, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h1068, h1078, hc34, hc45, hlam, hphi, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [h0, h1078, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1081_1]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    rcases p1081_3 (m.d 0 3) (by simp) with h1105 | h1105
                                    · linarith only [h1105, h924, hlam]
                                    · linarith only [h1105, h923, hlam]
                                  · have p1081_0 := h1081c.1
                                    have p1081_1 := h1081c.2.1
                                    have p1081_2 := h1081c.2.2.1
                                    have p1081_3 := h1081c.2.2.2
                                    linarith only [hlam, p1081_0]
                                · linarith only [h1073, h1080, h823, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1080, h3, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1073, h1080, h823, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1080, h921, hlam, ht01, ht12, u2elo4]
                        · linarith only [h1, h1068, h1073, h924, hc23, hc35, hlam, hphi]
                  · linarith only [h1068, h923, h924, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1115 | h1115
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1116 | h1116
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1117 | h1117
            · linarith only [h1117, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1119 | h1119
              · linarith only [h0, h1115, h1119, h823, h923, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1121 | h1121
                · linarith only [h0, h1121, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1123 | h1123
                  · linarith only [h1, h1123, h923, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1126 | h1126
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1127 | h1127
                        · linarith only [h1, h1125, h1127, h923, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1129 | h1129
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1130 | h1130
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1131 | h1131
                              · rcases h0emin with h1132 | h1132 | h1132 | h1132 | h1132
                                · rcases h3bigk with h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1125, h1131, hc03, hlam, hphi, ht0b, ht5b, p1133_1, u5ehi4]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h3, hlam, p1133_1]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h923, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1127, h1131, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1133_1, u5ehi4]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1117, hlam, p1133_1]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1123, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1, h1131, hc01, hlam, hphi, ht0b, ht5b, p1133_1, u5ehi4]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1127, hc03, hc34, hlam, hphi, p1133_1]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1127, hc13, hc34, hlam, hphi, p1133_1]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1127, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1127, h1131, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1133_1, u5ehi4]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1, h1125, h1131, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1133_1, u5ehi4]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1125, h1131, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1133_1, u5ehi4]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1129, h921, hc02, hc34, hlam, hphi, ht23, p1133_1]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    rcases p1133_3 (m.d 0 3) (by simp) with h1153 | h1153
                                    · linarith only [h1153, h923, hlam]
                                    · linarith only [h1115, h1153, hlam]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1115, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1125, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1129, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [h1131, hlam, p1133_0]
                                  · have p1133_0 := h1133c.1
                                    have p1133_1 := h1133c.2.1
                                    have p1133_2 := h1133c.2.2.1
                                    have p1133_3 := h1133c.2.2.2
                                    linarith only [hlam, p1133_0]
                                · linarith only [h1132, h921, hlam, ht01, ht12, u2elo4]
                                · linarith only [h1132, h3, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1132, h823, hlam, ht01, ht12, u2elo3]
                                · linarith only [h1132, h921, hlam, ht01, ht12, u2elo4]
                              · linarith only [h1127, h1129, h1131, h921, hc02, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1, h1125, h1126, h1130, h2, h823, h923, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h1, h1125, h1129, h3, hlam]
                      · linarith only [h1116, h1119, h1126, h823, hc12, hlam, hphi, u2elo3]
                    · linarith only [h1115, h1125, h923, hc13, hc34, hlam, hphi]
          · linarith only [h1115, h1116, h923, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1171 | h1171
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1172 | h1172
            · linarith only [h0, h1172, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
              · linarith only [h0, h1171, h1174, h2, h3, h823, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1176 | h1176
                · linarith only [h0, h1176, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1178 | h1178
                  · linarith only [h1, h1178, h923, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                    · linarith only [h1, h1115, h1180, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1182 | h1182
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1183 | h1183
                        · linarith only [h1183, h3, h923, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1185 | h1185
                          · linarith only [h0, h1115, h1185, h3, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1187 | h1187
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1188 | h1188
                              · rcases h0emin with h1189 | h1189 | h1189 | h1189 | h1189
                                · rcases h3bigk with h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c | h1190c
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1185, h3, hc13, hc35, hlam, hphi, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h3, hlam, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h923, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1115, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1172, hlam, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1178, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1180, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1185, hc03, hc35, hlam, hphi, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1185, hc13, hc35, hlam, hphi, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1183, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1185, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    rcases p1190_3 (m.d 0 3) (by simp) with h1206 | h1206
                                    · linarith only [h1206, hlam, p1190_0]
                                    · rcases p1190_3 (m.d 1 3) (by simp) with h1208 | h1208
                                      · linarith only [h1178, h1208, hlam]
                                      · rcases p1190_3 (m.d 2 3) (by simp) with h1210 | h1210
                                        · linarith only [h1183, h1210, hlam]
                                        · linarith only [h1210, h3, hlam]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    rcases p1190_3 (m.d 0 3) (by simp) with h1213 | h1213
                                    · linarith only [h1213, h923, hlam]
                                    · linarith only [h1, h1213, hlam]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h0, h1115, h3, hc12, hc34, hlam, hphi, ht23, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    rcases p1190_3 (m.d 0 3) (by simp) with h1219 | h1219
                                    · linarith only [h1219, hlam, p1190_0]
                                    · rcases p1190_3 (m.d 1 3) (by simp) with h1221 | h1221
                                      · linarith only [h1180, h1221, hlam]
                                      · rcases p1190_3 (m.d 2 3) (by simp) with h1223 | h1223
                                        · linarith only [h1185, h1223, hlam]
                                        · linarith only [h1223, h3, hlam]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    rcases p1190_3 (m.d 0 3) (by simp) with h1226 | h1226
                                    · linarith only [h1115, h1226, hlam]
                                    · linarith only [h1, h1226, hlam]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p1190_1]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [h1188, hlam, p1190_0]
                                  · have p1190_0 := h1190c.1
                                    have p1190_1 := h1190c.2.1
                                    have p1190_2 := h1190c.2.2.1
                                    have p1190_3 := h1190c.2.2.2
                                    linarith only [hlam, p1190_0]
                                · linarith only [h1189, h3, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1189, h3, hlam, ht01, ht12, u2elo2]
                                · linarith only [h1189, h823, hlam, ht01, ht12, u2elo3]
                                · linarith only [h1187, h1189, h921, hlam, ht01, ht12, u2elo3]
                              · linarith only [h1, h1172, h1182, h1187, h1188, h2, h921, h923, hc12, hlam, hphi, u2elo3]
                            · linarith only [h1171, h1187, h823, hlam]
                      · linarith only [h1171, h1174, h1182, h823, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1239 | h1239
            · linarith only [h0, h1239, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1241 | h1241
              · linarith only [h0, h1241, h823, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1243 | h1243
                · linarith only [h0, h1243, h3, h921, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1245 | h1245
                  · linarith only [h1, h1245, h923, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1247 | h1247
                    · linarith only [h1, h1115, h1247, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1249 | h1249
                      · linarith only [h0, h1171, h1241, h1249, h3, h923, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1251 | h1251
                        · linarith only [h0, h1251, h3, h923, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1253 | h1253
                          · linarith only [h0, h1115, h1251, h1253, h3, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1255 | h1255
                            · linarith only [h0, h1171, h1255, h3, h923, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
                              · linarith only [h0, h1251, h1255, h1257, h3, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1251, h1257, h3, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1260 | h1260
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1261 | h1261
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1262 | h1262
      · linarith only [h0, h1262, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1264 | h1264
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1265 | h1265
          · linarith only [h1260, h1262, h1265, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1267 | h1267
            · linarith only [h1261, h1262, h1267, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1269 | h1269
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1270 | h1270
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1271 | h1271
                  · linarith only [h0, h1262, h1265, h1271, h2, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1269, h1271, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h1261, h1269, h1270, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1260, h1262, h1269, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1276 | h1276
          · linarith only [h1261, h1262, h1264, h1276, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1278 | h1278
            · linarith only [h1261, h1262, h1278, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1280 | h1280
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1281 | h1281
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1282 | h1282
                  · linarith only [h1262, h1282, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1282, h2, hc12, hlam, hphi, u2elo4]
                · linarith only [h1261, h1262, h1280, h1281, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1260, h1262, h1280, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1287 | h1287
      · linarith only [h1261, h1287, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1289 | h1289
        · linarith only [h1260, h1261, h1289, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1291 | h1291
          · linarith only [h1260, h1261, h1291, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1293 | h1293
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1294 | h1294
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1295 | h1295
                · linarith only [h0, h1261, h1295, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h0, h1287, h1297, h2, hlam]
                  · linarith only [h0, h1294, h1297, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1260, h1261, h1294, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1301 | h1301
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1302 | h1302
                · linarith only [h0, h1261, h1302, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1304 | h1304
                  · linarith only [h0, h1287, h1304, h2, hlam]
                  · linarith only [h0, h1301, h1304, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1260, h1261, h1301, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1308 | h1308
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1309 | h1309
      · linarith only [h1260, h1309, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1311 | h1311
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1312 | h1312
          · linarith only [h1, h1312, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1314 | h1314
            · linarith only [h1260, h1308, h1314, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
              · linarith only [h0, h1260, h1316, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1318 | h1318
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1319 | h1319
                  · linarith only [h0, h1260, h1309, h1319, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                  · linarith only [h1, h1316, h1318, h1319, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1260, h1308, h1318, hc12, hlam, hphi, u2elo2]
        · linarith only [h1260, h1308, h1311, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1324 | h1324
      · linarith only [h1260, h1324, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1326 | h1326
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1327 | h1327
          · linarith only [h1, h1327, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1329 | h1329
            · linarith only [h1, h1326, h1329, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
              · linarith only [h1260, h1331, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1333 | h1333
                · linarith only [h1, h1308, h1331, h1333, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1335 | h1335
                  · linarith only [h0, h1324, h1335, h2, hlam]
                  · linarith only [h1, h1331, h1335, h2, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1338 | h1338
          · linarith only [h1, h1338, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1340 | h1340
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1341 | h1341
              · linarith only [h1260, h1341, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1343 | h1343
                · linarith only [h1, h1308, h1340, h1341, h1343, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1345 | h1345
                  · linarith only [h1, h1308, h1340, h1341, h1345, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h1, h1341, h1345, h2, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1348 | h1348
              · linarith only [h0, h1260, h1348, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1350 | h1350
                · linarith only [h0, h1308, h1350, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
                  · linarith only [h0, h1324, h1352, h2, hlam]
                  · linarith only [h1, h1348, h1352, h2, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1355 | h1355
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1356 | h1356
    · linarith only [h0, h1, h1356, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1358 | h1358
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1359 | h1359
        · linarith only [h1356, h1359, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1361 | h1361
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1362 | h1362
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1363 | h1363
              · linarith only [h1356, h1358, h1363, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
                · linarith only [h1356, h1365, hc02, hlam, hphi, u2elo1]
                · linarith only [h1, h1355, h1365, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · linarith only [h1, h1355, h1362, hlam]
          · linarith only [h1, h1355, h1358, h1359, h1361, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1370 | h1370
        · linarith only [h1356, h1370, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1372 | h1372
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1373 | h1373
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1374 | h1374
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1375 | h1375
                · linarith only [h0, h1, h1356, h1375, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1375, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1378 | h1378
                · linarith only [h0, h1356, h1373, h1378, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                · linarith only [h1, h1355, h1378, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · linarith only [h1, h1355, h1373, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1382 | h1382
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1383 | h1383
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1384 | h1384
                · linarith only [h0, h1, h1356, h1384, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1, h1355, h1384, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
              · linarith only [h1, h1355, h1372, h1383, hlam]
            · linarith only [h1, h1355, h1382, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1389 | h1389
    · linarith only [h0, h1, h1389, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1391 | h1391
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1392 | h1392
        · linarith only [h1389, h1392, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1394 | h1394
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1395 | h1395
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1396 | h1396
              · linarith only [h1389, h1391, h1396, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1398 | h1398
                · linarith only [h0, h1, h1389, h1398, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1398, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1401 | h1401
              · linarith only [h1389, h1391, h1401, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1403 | h1403
                · linarith only [h1389, h1403, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h1403, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h1391, h1394, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1407 | h1407
        · linarith only [h1389, h1407, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1410 | h1410
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1411 | h1411
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1412 | h1412
                · linarith only [h1389, h1412, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h1412, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
                · linarith only [h0, h1, h1389, h1415, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1415, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1418 | h1418
              · linarith only [h1409, h1410, h1418, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1420 | h1420
                · linarith only [h0, h1, h1410, h1420, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h1420, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1423 | h1423
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1424 | h1424
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1425 | h1425
                · linarith only [h0, h1, h1409, h1425, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h1425, hc12, hlam, hphi, u2elo2]
              · linarith only [h1409, h1423, h1424, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1429 | h1429
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1430 | h1430
                · linarith only [h0, h1, h1409, h1430, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h1430, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1433 | h1433
                · linarith only [h0, h1, h1409, h1433, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h1433, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1436 | h1436
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1437 | h1437
    · linarith only [h0, h1437, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1439 | h1439
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1440 | h1440
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1441 | h1441
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1442 | h1442
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1443 | h1443
              · linarith only [h0, h1436, h1443, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1445 | h1445
                · linarith only [h0, h1436, h1442, h1445, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1447 | h1447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1448 | h1448
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1449 | h1449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1450 | h1450
                        · linarith only [h1436, h1437, h1449, h1450, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h1436, h1437, h1442, h1449, h1450, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1441, h1449, hc12, hlam, hphi, u2elo0]
                    · linarith only [h0, h1441, h1448, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1447, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1456 | h1456
              · linarith only [h0, h1436, h1456, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1459 | h1459
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1460 | h1460
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1461 | h1461
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1462 | h1462
                        · linarith only [h1436, h1437, h1442, h1461, h1462, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1464 | h1464
                          · linarith only [h1436, h1437, h1456, h1461, h1464, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1466 | h1466
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1467 | h1467
                              · linarith only [h1437, h1462, h1466, h1467, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1469 | h1469
                                · linarith only [h1436, h1437, h1459, h1464, h1469, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1471 | h1471
                                  · linarith only [h1440, h1471, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1473 | h1473
                                    · rcases h0emin with h1474 | h1474 | h1474 | h1474 | h1474
                                      · linarith only [h1437, h1466, h1474, hc14, hlam, ht01]
                                      · linarith only [h0, h1474, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1436, h1437, h1466, h1474, hc14, hlam, ht01]
                                      · linarith only [h0, h1440, h1474, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1441, h1474, hlam, ht01, ht12, u2elo1]
                                    · linarith only [h0, h1440, h1442, h1458, h1473, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h0, h1437, h1440, h1458, h1466, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1440, h1458, h1461, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · linarith only [h0, h1436, h1459, h1460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1459, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1485 | h1485
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1486 | h1486
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1487 | h1487
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1488 | h1488
                        · linarith only [h1436, h1437, h1442, h1487, h1488, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1490 | h1490
                          · linarith only [h1436, h1437, h1456, h1487, h1490, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1492 | h1492
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1493 | h1493
                              · linarith only [h1436, h1437, h1458, h1485, h1488, h1492, h1493, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1495 | h1495
                                · linarith only [h1436, h1437, h1485, h1490, h1495, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1497 | h1497
                                  · linarith only [h1436, h1437, h1440, h1458, h1485, h1497, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1499 | h1499
                                    · rcases h0emin with h1500 | h1500 | h1500 | h1500 | h1500
                                      · linarith only [h1437, h1458, h1492, h1500, hc14, hlam, ht01]
                                      · linarith only [h0, h1500, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1436, h1500, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1436, h1458, h1485, h1488, h1492, h1500, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1436, h1458, h1485, h1488, h1492, h1500, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                                    · linarith only [h1488, h1492, h1499, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1507 | h1507
                              · linarith only [h1436, h1437, h1442, h1485, h1507, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1509 | h1509
                                · linarith only [h1436, h1437, h1485, h1487, h1509, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1511 | h1511
                                  · linarith only [h1440, h1492, h1511, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1513 | h1513
                                    · linarith only [h1436, h1437, h1485, h1492, h1513, hc23, hc34, hlam, hphi]
                                    · rcases h0emin with h1515 | h1515 | h1515 | h1515 | h1515
                                      · linarith only [h1437, h1487, h1515, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1515, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1436, h1437, h1487, h1515, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1440, h1515, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1437, h1487, h1515, hlam, ht01, ht12, u2elo1]
                      · linarith only [h0, h1441, h1487, hlam]
                    · linarith only [h0, h1441, h1486, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1436, h1485, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1524 | h1524
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1525 | h1525
              · linarith only [h0, h1436, h1525, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1527 | h1527
                · linarith only [h0, h1436, h1441, h1524, h1527, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1529 | h1529
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1530 | h1530
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1531 | h1531
                      · linarith only [h0, h1436, h1441, h1529, h1531, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1436, h1529, h1531, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1436, h1440, h1529, h1530, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1436, h1529, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1536 | h1536
              · linarith only [h0, h1436, h1536, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1538 | h1538
                · linarith only [h1440, h1441, h1538, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1542 | h1542
                      · linarith only [h0, h1436, h1441, h1540, h1542, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1436, h1540, h1542, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1436, h1440, h1540, h1541, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1436, h1540, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1547 | h1547
          · linarith only [h1440, h1547, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1549 | h1549
            · linarith only [h0, h1436, h1440, h1549, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1551 | h1551
              · linarith only [h0, h1436, h1440, h1551, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1553 | h1553
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1554 | h1554
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1555 | h1555
                    · linarith only [h0, h1440, h1555, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1436, h1554, h1555, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1554, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1559 | h1559
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1560 | h1560
                    · linarith only [h0, h1436, h1440, h1559, h1560, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1436, h1559, h1560, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1436, h1559, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1436, h1439, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1565 | h1565
    · linarith only [h0, h1565, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1567 | h1567
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1568 | h1568
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1569 | h1569
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1570 | h1570
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1571 | h1571
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1572 | h1572
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1573 | h1573
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1574 | h1574
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1575 | h1575
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1576 | h1576
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1577 | h1577
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1578 | h1578
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1579 | h1579
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1580 | h1580
                                · linarith only [h1567, h1580, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1436, h1571, h1573, h1579, h1580, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1583 | h1583
                                · linarith only [h0, h1567, h1583, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1585 | h1585
                                  · linarith only [h1436, h1570, h1573, h1579, h1585, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1587 | h1587
                                    · linarith only [h1436, h1570, h1573, h1579, h1585, h1587, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                    · linarith only [h0, h1568, h1572, h1579, h1587, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1436, h1565, h1570, h1572, h1573, h1578, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h1436, h1571, h1577, hlam]
                        · linarith only [h1436, h1570, h1576, hlam]
                      · linarith only [h1436, h1571, h1573, h1575, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                    · linarith only [h1436, h1570, h1572, h1573, h1574, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · linarith only [h0, h1569, h1573, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1596 | h1596
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1597 | h1597
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1598 | h1598
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1599 | h1599
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1600 | h1600
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1601 | h1601
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1602 | h1602
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1603 | h1603
                                · linarith only [h1567, h1603, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1436, h1571, h1596, h1602, h1603, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h1570, h1572, h1596, h1599, h1601, h1602, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1607 | h1607
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1608 | h1608
                                · linarith only [h0, h1567, h1608, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · linarith only [h1436, h1571, h1596, h1607, h1608, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1611 | h1611
                                · linarith only [h1436, h1570, h1596, h1607, h1611, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1613 | h1613
                                  · linarith only [h0, h1568, h1601, h1613, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1615 | h1615
                                    · linarith only [h1570, h1572, h1615, hlam]
                                    · rcases h0emin with h1617 | h1617 | h1617 | h1617 | h1617
                                      · linarith only [h0, h1617, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1617, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1436, h1596, h1617, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1436, h1571, h1572, h1596, h1607, h1615, h1617, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u2elo1]
                                      · linarith only [h0, h1569, h1617, hlam, ht01, ht12, u2elo1]
                          · linarith only [h1436, h1571, h1600, hlam]
                        · linarith only [h1436, h1570, h1599, hlam]
                      · linarith only [h1436, h1596, h1598, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1436, h1571, h1596, h1597, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                  · linarith only [h0, h1569, h1596, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1628 | h1628
                · linarith only [h1570, h1571, h1628, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1630 | h1630
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1631 | h1631
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1632 | h1632
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1633 | h1633
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1634 | h1634
                          · linarith only [h1570, h1571, h1630, h1634, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1636 | h1636
                            · linarith only [h1633, h1634, h1636, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1638 | h1638
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1639 | h1639
                                · linarith only [h1436, h1634, h1639, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1641 | h1641
                                  · linarith only [h1565, h1636, h1641, hc01, hlam, hphi, ht12, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1643 | h1643
                                    · linarith only [h0, h1569, h1628, h1638, h1639, h1643, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases h0emin with h1645 | h1645 | h1645 | h1645 | h1645
                                      · linarith only [h1436, h1645, hc13, hlam, ht01]
                                      · linarith only [h0, h1645, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1436, h1634, h1643, h1645, hc45, hlam, ht01, ht12, ht23, ht34]
                                      · linarith only [h0, h1568, h1645, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1569, h1645, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1436, h1570, h1634, h1638, hc23, hc35, hlam, hphi]
                        · linarith only [h1436, h1570, h1571, h1633, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h1569, h1632, hlam]
                    · linarith only [h0, h1569, h1631, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1569, h1630, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1656 | h1656
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1657 | h1657
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1658 | h1658
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1659 | h1659
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1660 | h1660
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1661 | h1661
                        · linarith only [h1570, h1656, h1661, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1664 | h1664
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1665 | h1665
                              · linarith only [h1567, h1661, h1663, h1665, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1667 | h1667
                                · linarith only [h0, h1568, h1665, h1667, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · linarith only [h1436, h1656, h1661, h1667, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h1436, h1568, h1656, h1657, h1661, h1664, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                          · linarith only [h1436, h1656, h1663, hlam]
                      · linarith only [h0, h1660, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1568, h1659, hlam]
                  · linarith only [h0, h1568, h1570, h1656, h1658, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · linarith only [h1570, h1656, h1657, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1676 | h1676
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1677 | h1677
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1679 | h1679
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
                        · linarith only [h1436, h1570, h1677, h1680, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1682 | h1682
                          · linarith only [h1656, h1680, h1682, hc03, hc34, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                              · linarith only [h1436, h1680, h1685, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1687 | h1687
                                · linarith only [h1436, h1682, h1687, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1689 | h1689
                                  · linarith only [h1568, h1689, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1691 | h1691
                                    · rcases h0emin with h1692 | h1692 | h1692 | h1692 | h1692
                                      · linarith only [h0, h1692, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h0, h1692, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1436, h1682, h1691, h1692, hc34, hlam, ht01, ht12, ht23]
                                      · linarith only [h0, h1568, h1692, hlam, ht01, ht12, u2elo1]
                                      · linarith only [h1565, h1678, h1684, h1692, hlam, ht01, ht12, u2elo1]
                                    · linarith only [h0, h1568, h1570, h1676, h1691, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h0, h1436, h1568, h1676, h1680, h1684, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1568, h1676, h1679, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · linarith only [h0, h1568, h1676, h1678, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · linarith only [h0, h1568, h1676, h1677, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1704 | h1704
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1705 | h1705
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1706 | h1706
                        · linarith only [h1436, h1570, h1703, h1706, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1708 | h1708
                          · linarith only [h1436, h1656, h1706, h1708, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1710 | h1710
                            · linarith only [h1436, h1570, h1676, h1704, h1710, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1712 | h1712
                              · linarith only [h1567, h1570, h1712, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1714 | h1714
                                · linarith only [h0, h1568, h1708, h1712, h1714, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1716 | h1716
                                  · linarith only [h0, h1568, h1710, h1716, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1718 | h1718
                                    · linarith only [h1436, h1706, h1710, h1718, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1436, h1706, h1718, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1569, h1705, hlam]
                    · linarith only [h0, h1569, h1704, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1569, h1703, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1724 | h1724
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1725 | h1725
              · linarith only [h1567, h1569, h1725, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1727 | h1727
                · linarith only [h1568, h1569, h1727, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1729 | h1729
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1730 | h1730
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1731 | h1731
                      · linarith only [h1569, h1731, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1731, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1436, h1729, h1730, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h1567, h1729, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1736 | h1736
              · linarith only [h1568, h1569, h1724, h1736, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1738 | h1738
                · linarith only [h1568, h1569, h1738, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1740 | h1740
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1741 | h1741
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1742 | h1742
                      · linarith only [h1569, h1742, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1742, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1436, h1740, h1741, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h1567, h1740, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1747 | h1747
          · linarith only [h1568, h1747, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1749 | h1749
            · linarith only [h1567, h1568, h1749, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1751 | h1751
              · linarith only [h1567, h1568, h1751, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1753 | h1753
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1754 | h1754
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1755 | h1755
                    · linarith only [h1568, h1755, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1755, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1567, h1568, h1754, hc01, hlam, hphi, ht12, u2elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1759 | h1759
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1760 | h1760
                    · linarith only [h1568, h1760, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1760, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1759, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1764 | h1764
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1765 | h1765
          · linarith only [h1567, h1765, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1767 | h1767
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1768 | h1768
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1769 | h1769
                · linarith only [h1567, h1764, h1769, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1771 | h1771
                  · linarith only [h1567, h1771, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1771, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1774 | h1774
                · linarith only [h1567, h1764, h1774, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1776 | h1776
                  · linarith only [h1567, h1776, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1776, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1567, h1764, h1767, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1780 | h1780
          · linarith only [h1567, h1780, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1782 | h1782
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1783 | h1783
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1784 | h1784
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1785 | h1785
                  · linarith only [h1567, h1785, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1785, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1788 | h1788
                  · linarith only [h0, h1567, h1788, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1788, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1791 | h1791
                · linarith only [h1782, h1783, h1791, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1793 | h1793
                  · linarith only [h0, h1567, h1793, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1793, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1796 | h1796
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1797 | h1797
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1798 | h1798
                  · linarith only [h0, h1567, h1798, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1798, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1782, h1796, h1797, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1802 | h1802
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1803 | h1803
                  · linarith only [h0, h1567, h1803, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1803, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1806 | h1806
                  · linarith only [h0, h1567, h1806, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1806, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
