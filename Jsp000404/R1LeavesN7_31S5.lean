import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h740 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h898 | h898
  · linarith only [h4, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h900 | h900
    · rcases m.htr 0 3 5 (by decide) (by decide) with h901 | h901
      · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
        · rcases m.htr 1 2 3 (by decide) (by decide) with h903 | h903
          · linarith only [h0, h4, h903, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h905 | h905
            · linarith only [h0, h740, h902, h905, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
              · linarith only [h0, h898, h907, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
                · rcases m.htr 1 3 5 (by decide) (by decide) with h910 | h910
                  · linarith only [h1, h910, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h912 | h912
                    · linarith only [h4, h901, h909, h910, h912, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                            · linarith only [h4, h901, h905, h909, h910, h912, h917, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                rcases p919_3 (m.d 0 1) (by simp) with h921 | h921
                                · rcases p919_3 (m.d 0 2) (by simp) with h922 | h922
                                  · linarith only [h0, h922, hlam]
                                  · rcases p919_3 (m.d 0 3) (by simp) with h924 | h924
                                    · linarith only [h1, h924, hlam]
                                    · linarith only [h4, h924, hlam]
                                · linarith only [h0, h921, hlam]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h900, h902, h910, h917, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h902, h909, h910, h917, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p919_1, u5ehi0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h0, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h4, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h740, hlam, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h898, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h1, hlam, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                rcases p919_3 (m.d 0 1) (by simp) with h937 | h937
                                · rcases p919_3 (m.d 0 2) (by simp) with h938 | h938
                                  · linarith only [h4, h938, hlam]
                                  · rcases p919_3 (m.d 0 3) (by simp) with h940 | h940
                                    · rcases p919_3 (m.d 0 4) (by simp) with h941 | h941
                                      · linarith only [h900, h941, hlam]
                                      · linarith only [h740, h941, hlam]
                                    · linarith only [h4, h940, hlam]
                                · linarith only [h0, h937, hlam]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h902, h909, h910, h917, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h4, h902, h909, h910, h917, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h2, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                rcases p919_3 (m.d 0 1) (by simp) with h950 | h950
                                · rcases p919_3 (m.d 0 2) (by simp) with h951 | h951
                                  · linarith only [h740, h951, hlam]
                                  · rcases p919_3 (m.d 0 3) (by simp) with h953 | h953
                                    · rcases p919_3 (m.d 0 4) (by simp) with h954 | h954
                                      · rcases p919_3 (m.d 0 5) (by simp) with h955 | h955
                                        · linarith only [h902, h955, hlam]
                                        · linarith only [h898, h955, hlam]
                                      · linarith only [h740, h954, hlam]
                                    · linarith only [h4, h953, hlam]
                                · linarith only [h0, h950, hlam]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h900, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h740, h902, h909, h910, h914, h917, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h3, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                rcases p919_3 (m.d 0 1) (by simp) with h965 | h965
                                · rcases p919_3 (m.d 0 2) (by simp) with h966 | h966
                                  · linarith only [h898, h966, hlam]
                                  · rcases p919_3 (m.d 0 3) (by simp) with h968 | h968
                                    · rcases p919_3 (m.d 0 4) (by simp) with h969 | h969
                                      · rcases p919_3 (m.d 0 5) (by simp) with h970 | h970
                                        · rcases h2bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p919_1, p971_1]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h4, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h740, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h898, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h0, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h903, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h905, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h907, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            rcases p971_3 (m.d 0 2) (by simp) with h982 | h982
                                            · linarith only [h982, hlam, p971_0]
                                            · rcases p971_3 (m.d 1 2) (by simp) with h984 | h984
                                              · linarith only [h903, h984, hlam]
                                              · rcases p971_3 (m.d 2 3) (by simp) with h986 | h986
                                                · rcases p971_3 (m.d 2 4) (by simp) with h987 | h987
                                                  · linarith only [h914, h987, hlam]
                                                  · linarith only [h740, h987, hlam]
                                                · linarith only [h986, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            rcases p971_3 (m.d 0 2) (by simp) with h991 | h991
                                            · linarith only [h4, h991, hlam]
                                            · linarith only [h0, h991, hlam]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h740, h902, h909, h910, h917, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p971_1]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h898, hc02, hc23, hlam, hphi, p919_1, p971_1]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            rcases p971_3 (m.d 0 2) (by simp) with h997 | h997
                                            · linarith only [h997, hlam, p971_0]
                                            · rcases p971_3 (m.d 1 2) (by simp) with h999 | h999
                                              · linarith only [h905, h999, hlam]
                                              · rcases p971_3 (m.d 2 3) (by simp) with h1001 | h1001
                                                · rcases p971_3 (m.d 2 4) (by simp) with h1002 | h1002
                                                  · rcases p971_3 (m.d 2 5) (by simp) with h1003 | h1003
                                                    · linarith only [h1003, h916, hlam]
                                                    · linarith only [h1003, h898, hlam]
                                                  · linarith only [h1002, hlam, p971_0]
                                                · linarith only [h1001, h4, hlam]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            rcases p971_3 (m.d 0 2) (by simp) with h1008 | h1008
                                            · linarith only [h1008, h740, hlam]
                                            · linarith only [h0, h1008, hlam]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h914, hlam, p971_1]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h0, h898, hc12, hc24, hlam, hphi, p919_1, p971_1]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            rcases p971_3 (m.d 0 2) (by simp) with h1014 | h1014
                                            · linarith only [h1014, hlam, p971_0]
                                            · rcases p971_3 (m.d 1 2) (by simp) with h1016 | h1016
                                              · linarith only [h1016, h907, hlam]
                                              · rcases p971_3 (m.d 2 3) (by simp) with h1018 | h1018
                                                · rcases p971_3 (m.d 2 4) (by simp) with h1019 | h1019
                                                  · rcases p971_3 (m.d 2 5) (by simp) with h1020 | h1020
                                                    · rcases h3bigk with h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        rcases p1021_3 (m.d 0 3) (by simp) with h1023 | h1023
                                                        · rcases p1021_3 (m.d 1 3) (by simp) with h1024 | h1024
                                                          · linarith only [h1, h1024, hlam]
                                                          · rcases p1021_3 (m.d 2 3) (by simp) with h1026 | h1026
                                                            · rcases p1021_3 (m.d 3 4) (by simp) with h1027 | h1027
                                                              · linarith only [h1027, h900, hlam]
                                                              · rcases p1021_3 (m.d 3 5) (by simp) with h1029 | h1029
                                                                · linarith only [h1029, h901, hlam]
                                                                · linarith only [h1029, h910, hlam]
                                                            · linarith only [h1026, h903, hlam]
                                                        · linarith only [h1, h1023, hlam]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h4, hlam, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h900, h902, h909, h910, h917, hlam, p1021_2]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h909, h910, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h1, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h903, hlam, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h902, h910, h917, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h910, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h900, h902, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1021_1, u5ehi3]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        rcases p1021_3 (m.d 0 3) (by simp) with h1043 | h1043
                                                        · linarith only [h1043, h4, hlam]
                                                        · linarith only [h1, h1043, hlam]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h4, h900, h902, h909, h910, h917, hlam, p1021_2]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h909, h910, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h900, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h909, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h914, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h917, hlam, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h901, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h900, h902, h909, h917, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1021_1]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [h915, hlam, p1021_0]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        rcases p1021_3 (m.d 0 3) (by simp) with h1057 | h1057
                                                        · rcases p1021_3 (m.d 1 3) (by simp) with h1058 | h1058
                                                          · linarith only [h1058, h910, hlam]
                                                          · linarith only [h1058, h909, hlam]
                                                        · linarith only [h1057, h900, hlam]
                                                      · have p1021_0 := h1021c.1
                                                        have p1021_1 := h1021c.2.1
                                                        have p1021_2 := h1021c.2.2.1
                                                        have p1021_3 := h1021c.2.2.2
                                                        linarith only [hlam, p1021_0]
                                                    · linarith only [h1020, hlam, p971_0]
                                                  · linarith only [h1019, h740, hlam]
                                                · linarith only [h1018, h4, hlam]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            rcases p971_3 (m.d 0 2) (by simp) with h1066 | h1066
                                            · linarith only [h1066, h898, hlam]
                                            · linarith only [h0, h1066, hlam]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h915, hlam, p971_1]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [h916, hlam, p971_0]
                                          · have p971_0 := h971c.1
                                            have p971_1 := h971c.2.1
                                            have p971_2 := h971c.2.2.1
                                            have p971_3 := h971c.2.2.2
                                            linarith only [hlam, p971_0]
                                        · linarith only [h898, h970, hlam]
                                      · linarith only [h740, h969, hlam]
                                    · linarith only [h4, h968, hlam]
                                · linarith only [h0, h965, hlam]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h901, hlam, p919_0]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [h902, hlam, p919_1]
                              · have p919_0 := h919c.1
                                have p919_1 := h919c.2.1
                                have p919_2 := h919c.2.2.1
                                have p919_3 := h919c.2.2.2
                                linarith only [hlam, p919_0]
                          · linarith only [h0, h4, h740, h900, h902, h916, hc12, hc23, hlam, hphi]
                        · linarith only [h4, h900, h902, h915, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h4, h900, h902, h909, h912, h914, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1082 | h1082
                  · linarith only [h1, h1082, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1084 | h1084
                    · linarith only [h1084, h4, h900, h909, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1086 | h1086
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1087 | h1087
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1088 | h1088
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1089 | h1089
                            · linarith only [h1084, h1089, h4, h900, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                            · linarith only [h1089, h740, h902, h903, h909, hc12, hc24, hlam, hphi]
                          · linarith only [h0, h1088, h4, h740, h900, h902, hc12, hc23, hlam, hphi]
                        · linarith only [h1087, h4, h900, h902, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h1084, h1086, h4, h900, h902, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1095 | h1095
          · linarith only [h0, h1095, h4, h901, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1097 | h1097
            · linarith only [h0, h1097, h740, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1099 | h1099
              · linarith only [h0, h1099, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1101 | h1101
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1102 | h1102
                  · linarith only [h1, h1102, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
                    · linarith only [h1101, h1102, h1104, h901, h902, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1106 | h1106
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1107 | h1107
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1108 | h1108
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1109 | h1109
                            · linarith only [h1, h1109, h900, h902, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · rcases h0bigk with h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                rcases p1111_3 (m.d 0 1) (by simp) with h1113 | h1113
                                · rcases p1111_3 (m.d 0 2) (by simp) with h1114 | h1114
                                  · linarith only [h0, h1114, hlam]
                                  · rcases p1111_3 (m.d 0 3) (by simp) with h1116 | h1116
                                    · linarith only [h1, h1116, hlam]
                                    · linarith only [h1116, h4, hlam]
                                · linarith only [h0, h1113, hlam]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h1101, h1102, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                rcases p1111_3 (m.d 0 1) (by simp) with h1121 | h1121
                                · rcases p1111_3 (m.d 0 2) (by simp) with h1122 | h1122
                                  · linarith only [h0, h1122, hlam]
                                  · rcases p1111_3 (m.d 0 3) (by simp) with h1124 | h1124
                                    · linarith only [h1, h1124, hlam]
                                    · linarith only [h1124, h900, hlam]
                                · linarith only [h1121, h2, hlam]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h1101, h1102, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h0, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h4, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h740, hlam, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h898, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h1, hlam, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                rcases p1111_3 (m.d 0 1) (by simp) with h1135 | h1135
                                · rcases p1111_3 (m.d 0 2) (by simp) with h1136 | h1136
                                  · linarith only [h1136, h4, hlam]
                                  · rcases p1111_3 (m.d 0 3) (by simp) with h1138 | h1138
                                    · rcases p1111_3 (m.d 0 4) (by simp) with h1139 | h1139
                                      · linarith only [h1139, h900, hlam]
                                      · linarith only [h1139, h740, hlam]
                                    · linarith only [h1138, h4, hlam]
                                · linarith only [h0, h1135, hlam]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                rcases p1111_3 (m.d 0 1) (by simp) with h1145 | h1145
                                · rcases p1111_3 (m.d 0 2) (by simp) with h1146 | h1146
                                  · linarith only [h1146, h4, hlam]
                                  · rcases p1111_3 (m.d 0 3) (by simp) with h1148 | h1148
                                    · rcases p1111_3 (m.d 0 4) (by simp) with h1149 | h1149
                                      · linarith only [h1149, h900, hlam]
                                      · rcases p1111_3 (m.d 0 5) (by simp) with h1151 | h1151
                                        · linarith only [h1151, h901, hlam]
                                        · linarith only [h1151, h902, hlam]
                                    · linarith only [h1148, h900, hlam]
                                · linarith only [h1145, h2, hlam]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h1101, h1102, h901, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h2, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h0, h1108, h902, hc12, hc24, hlam, hphi, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h900, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h902, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h3, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h0, h1108, h902, hc12, hc24, hlam, hphi, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h901, hlam, p1111_0]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [h0, h1108, h740, h902, hc12, hc24, hlam, hphi, p1111_1]
                              · have p1111_0 := h1111c.1
                                have p1111_1 := h1111c.2.1
                                have p1111_2 := h1111c.2.2.1
                                have p1111_3 := h1111c.2.2.2
                                linarith only [hlam, p1111_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1167 | h1167
                            · linarith only [h1101, h1102, h1108, h1167, h901, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h0bigk with h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                rcases p1169_3 (m.d 0 1) (by simp) with h1171 | h1171
                                · rcases p1169_3 (m.d 0 2) (by simp) with h1172 | h1172
                                  · linarith only [h0, h1172, hlam]
                                  · rcases p1169_3 (m.d 0 3) (by simp) with h1174 | h1174
                                    · linarith only [h1, h1174, hlam]
                                    · linarith only [h1174, h4, hlam]
                                · linarith only [h0, h1171, hlam]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h1102, h901, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1169_1]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                rcases p1169_3 (m.d 0 1) (by simp) with h1179 | h1179
                                · rcases p1169_3 (m.d 0 2) (by simp) with h1180 | h1180
                                  · linarith only [h0, h1180, hlam]
                                  · rcases p1169_3 (m.d 0 3) (by simp) with h1182 | h1182
                                    · linarith only [h1, h1182, hlam]
                                    · linarith only [h1182, h900, hlam]
                                · linarith only [h1179, h2, hlam]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1169_1, u5ehi0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h0, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h4, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h740, hlam, p1169_1]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h898, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h1, hlam, p1169_1]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                rcases p1169_3 (m.d 0 1) (by simp) with h1193 | h1193
                                · rcases p1169_3 (m.d 0 2) (by simp) with h1194 | h1194
                                  · linarith only [h1194, h4, hlam]
                                  · rcases p1169_3 (m.d 0 3) (by simp) with h1196 | h1196
                                    · rcases p1169_3 (m.d 0 4) (by simp) with h1197 | h1197
                                      · linarith only [h1197, h900, hlam]
                                      · linarith only [h1197, h740, hlam]
                                    · linarith only [h1196, h4, hlam]
                                · linarith only [h0, h1193, hlam]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                rcases p1169_3 (m.d 0 1) (by simp) with h1203 | h1203
                                · rcases p1169_3 (m.d 0 2) (by simp) with h1204 | h1204
                                  · linarith only [h1204, h4, hlam]
                                  · rcases p1169_3 (m.d 0 3) (by simp) with h1206 | h1206
                                    · rcases p1169_3 (m.d 0 4) (by simp) with h1207 | h1207
                                      · linarith only [h1207, h900, hlam]
                                      · rcases p1169_3 (m.d 0 5) (by simp) with h1209 | h1209
                                        · linarith only [h1209, h901, hlam]
                                        · linarith only [h1209, h902, hlam]
                                    · linarith only [h1206, h900, hlam]
                                · linarith only [h1203, h2, hlam]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h1101, h1102, h901, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1169_1]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h2, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h0, h902, hc12, hc45, hlam, hphi, ht23, ht34, p1169_1]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h900, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h902, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h3, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                rcases p1169_3 (m.d 0 1) (by simp) with h1221 | h1221
                                · rcases p1169_3 (m.d 0 2) (by simp) with h1222 | h1222
                                  · linarith only [h1222, h898, hlam]
                                  · rcases p1169_3 (m.d 0 3) (by simp) with h1224 | h1224
                                    · rcases p1169_3 (m.d 0 4) (by simp) with h1225 | h1225
                                      · linarith only [h1225, h902, hlam]
                                      · linarith only [h1225, h740, hlam]
                                    · linarith only [h1224, h4, hlam]
                                · linarith only [h0, h1221, hlam]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [h901, hlam, p1169_0]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                rcases p1169_3 (m.d 0 1) (by simp) with h1231 | h1231
                                · rcases p1169_3 (m.d 0 2) (by simp) with h1232 | h1232
                                  · linarith only [h1232, h898, hlam]
                                  · rcases p1169_3 (m.d 0 3) (by simp) with h1234 | h1234
                                    · rcases p1169_3 (m.d 0 4) (by simp) with h1235 | h1235
                                      · linarith only [h1235, h902, hlam]
                                      · rcases p1169_3 (m.d 0 5) (by simp) with h1237 | h1237
                                        · rcases h2bigk with h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h740, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1169_1, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h4, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h740, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h898, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h0, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1095, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1097, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1099, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            rcases p1238_3 (m.d 0 2) (by simp) with h1249 | h1249
                                            · linarith only [h1249, hlam, p1238_0]
                                            · rcases p1238_3 (m.d 1 2) (by simp) with h1251 | h1251
                                              · linarith only [h1095, h1251, hlam]
                                              · rcases p1238_3 (m.d 2 3) (by simp) with h1253 | h1253
                                                · rcases p1238_3 (m.d 2 4) (by simp) with h1254 | h1254
                                                  · linarith only [h1106, h1254, hlam]
                                                  · linarith only [h1254, h740, hlam]
                                                · linarith only [h1253, hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            rcases p1238_3 (m.d 0 2) (by simp) with h1258 | h1258
                                            · linarith only [h1258, h4, hlam]
                                            · linarith only [h0, h1258, hlam]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h740, hc02, hc23, hlam, hphi, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h898, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1169_1, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h0, h1108, hc12, hc45, hlam, hphi, ht23, ht34, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1108, hc12, hc45, hlam, hphi, ht23, ht34, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1106, hlam, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [hlam, p1238_0]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1108, hlam, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            rcases p1238_3 (m.d 0 2) (by simp) with h1269 | h1269
                                            · linarith only [h1269, hlam, p1238_0]
                                            · rcases p1238_3 (m.d 1 2) (by simp) with h1271 | h1271
                                              · linarith only [h1099, h1271, hlam]
                                              · rcases p1238_3 (m.d 2 3) (by simp) with h1273 | h1273
                                                · rcases p1238_3 (m.d 2 4) (by simp) with h1274 | h1274
                                                  · linarith only [h1108, h1274, hlam]
                                                  · linarith only [h1274, h740, hlam]
                                                · linarith only [h1273, h4, hlam]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            rcases p1238_3 (m.d 0 2) (by simp) with h1278 | h1278
                                            · linarith only [h1278, h898, hlam]
                                            · linarith only [h0, h1278, hlam]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h1107, hlam, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [h0, h740, hc12, hc25, hlam, hphi, p1238_1]
                                          · have p1238_0 := h1238c.1
                                            have p1238_1 := h1238c.2.1
                                            have p1238_2 := h1238c.2.2.1
                                            have p1238_3 := h1238c.2.2.2
                                            linarith only [hlam, p1238_0]
                                        · linarith only [h1237, h902, hlam]
                                    · linarith only [h1234, h900, hlam]
                                · linarith only [h1231, h2, hlam]
                              · have p1169_0 := h1169c.1
                                have p1169_1 := h1169c.2.1
                                have p1169_2 := h1169c.2.2.1
                                have p1169_3 := h1169c.2.2.2
                                linarith only [hlam, p1169_0]
                        · linarith only [h1107, h4, h901, hlam]
                      · linarith only [h1101, h1102, h1106, h4, h901, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1290 | h1290
                  · linarith only [h1101, h1290, h900, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1292 | h1292
                    · linarith only [h1292, h2, h902, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1295 | h1295
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1296 | h1296
                          · linarith only [h1095, h1101, h1294, h1296, h900, h902, hc12, hc23, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1298 | h1298
                            · linarith only [h0, h1296, h1298, h740, hc12, hc34, hlam, hphi, ht23]
                            · rcases h0bigk with h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c | h1300c
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                rcases p1300_3 (m.d 0 1) (by simp) with h1302 | h1302
                                · rcases p1300_3 (m.d 0 2) (by simp) with h1303 | h1303
                                  · linarith only [h0, h1303, hlam]
                                  · rcases p1300_3 (m.d 0 3) (by simp) with h1305 | h1305
                                    · linarith only [h1, h1305, hlam]
                                    · linarith only [h1305, h4, hlam]
                                · linarith only [h0, h1302, hlam]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h901, hc01, hlam, hphi, ht0b, ht5b, p1300_1, u5ehi3]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                rcases p1300_3 (m.d 0 1) (by simp) with h1310 | h1310
                                · rcases p1300_3 (m.d 0 2) (by simp) with h1311 | h1311
                                  · linarith only [h0, h1311, hlam]
                                  · rcases p1300_3 (m.d 0 3) (by simp) with h1313 | h1313
                                    · linarith only [h1, h1313, hlam]
                                    · linarith only [h1313, h900, hlam]
                                · linarith only [h1310, h2, hlam]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1290, h901, hc01, hlam, hphi, ht0b, ht5b, p1300_1, u5ehi1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h0, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h4, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h740, hlam, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h898, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1, hlam, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                rcases p1300_3 (m.d 0 1) (by simp) with h1324 | h1324
                                · rcases p1300_3 (m.d 0 2) (by simp) with h1325 | h1325
                                  · linarith only [h1325, h4, hlam]
                                  · rcases p1300_3 (m.d 0 3) (by simp) with h1327 | h1327
                                    · rcases p1300_3 (m.d 0 4) (by simp) with h1328 | h1328
                                      · linarith only [h1328, h900, hlam]
                                      · linarith only [h1328, h740, hlam]
                                    · linarith only [h1327, h4, hlam]
                                · linarith only [h0, h1324, hlam]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1095, h1101, h4, h900, hc12, hc23, hlam, hphi, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1290, h4, h901, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1300_1, u5ehi1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h2, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h0, h1296, h740, hc12, hc45, hlam, hphi, ht23, ht34, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h900, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h902, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h3, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                rcases p1300_3 (m.d 0 1) (by simp) with h1342 | h1342
                                · rcases p1300_3 (m.d 0 2) (by simp) with h1343 | h1343
                                  · linarith only [h1343, h898, hlam]
                                  · rcases p1300_3 (m.d 0 3) (by simp) with h1345 | h1345
                                    · rcases p1300_3 (m.d 0 4) (by simp) with h1346 | h1346
                                      · linarith only [h1346, h902, hlam]
                                      · linarith only [h1346, h740, hlam]
                                    · linarith only [h1345, h4, hlam]
                                · linarith only [h0, h1342, hlam]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h901, hlam, p1300_0]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [h1095, h1101, h898, h900, hc12, hc25, hlam, hphi, p1300_1]
                              · have p1300_0 := h1300c.1
                                have p1300_1 := h1300c.2.1
                                have p1300_2 := h1300c.2.2.1
                                have p1300_3 := h1300c.2.2.2
                                linarith only [hlam, p1300_0]
                        · linarith only [h1095, h1101, h1295, h4, h900, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1294, h4, h900, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1356 | h1356
        · linarith only [h1356, h900, h901, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1358 | h1358
          · linarith only [h0, h1358, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1360 | h1360
            · linarith only [h0, h1360, h740, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1362 | h1362
              · linarith only [h0, h1362, h740, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1364 | h1364
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1365 | h1365
                  · linarith only [h1, h1365, h901, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1367 | h1367
                    · linarith only [h1356, h1367, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1369 | h1369
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1370 | h1370
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1371 | h1371
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1372 | h1372
                            · linarith only [h1356, h1370, h1372, h900, h901, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases h0bigk with h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                rcases p1374_3 (m.d 0 1) (by simp) with h1376 | h1376
                                · rcases p1374_3 (m.d 0 2) (by simp) with h1377 | h1377
                                  · linarith only [h0, h1377, hlam]
                                  · rcases p1374_3 (m.d 0 3) (by simp) with h1379 | h1379
                                    · linarith only [h1, h1379, hlam]
                                    · linarith only [h1379, h4, hlam]
                                · linarith only [h0, h1376, hlam]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                rcases p1374_3 (m.d 0 1) (by simp) with h1383 | h1383
                                · rcases p1374_3 (m.d 0 2) (by simp) with h1384 | h1384
                                  · linarith only [h0, h1384, hlam]
                                  · rcases p1374_3 (m.d 0 3) (by simp) with h1386 | h1386
                                    · linarith only [h1, h1386, hlam]
                                    · rcases p1374_3 (m.d 0 4) (by simp) with h1388 | h1388
                                      · linarith only [h1388, h2, hlam]
                                      · rcases p1374_3 (m.d 0 5) (by simp) with h1390 | h1390
                                        · linarith only [h1390, h3, hlam]
                                        · linarith only [h1390, h901, hlam]
                                · linarith only [h1, h1383, hlam]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                rcases p1374_3 (m.d 0 1) (by simp) with h1394 | h1394
                                · rcases p1374_3 (m.d 0 2) (by simp) with h1395 | h1395
                                  · linarith only [h0, h1395, hlam]
                                  · rcases p1374_3 (m.d 0 3) (by simp) with h1397 | h1397
                                    · linarith only [h1, h1397, hlam]
                                    · linarith only [h1397, h900, hlam]
                                · linarith only [h1394, h2, hlam]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1374_1, u5ehi1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h0, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h4, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h740, hlam, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h898, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h1, hlam, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h0, h1369, h1371, h1372, h901, hc12, hc23, hlam, hphi, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h0, h1369, h1371, h1372, h740, h901, hc12, hc23, hlam, hphi, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h901, hlam, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h2, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h0, h1369, h1371, h1372, h900, h901, hc12, hc23, hlam, hphi, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h900, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h1356, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h3, hlam, p1374_0]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h0, h1369, h1371, h1372, h901, hc12, hc23, hlam, hphi, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h1, h1364, h1369, h1371, h1372, h901, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [h1360, h1369, h1371, h1372, h2, h901, hc12, hc23, hlam, hphi, p1374_1]
                              · have p1374_0 := h1374c.1
                                have p1374_1 := h1374c.2.1
                                have p1374_2 := h1374c.2.2.1
                                have p1374_3 := h1374c.2.2.2
                                linarith only [hlam, p1374_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1422 | h1422
                            · linarith only [h1, h1364, h1422, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases h0bigk with h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                rcases p1424_3 (m.d 0 1) (by simp) with h1426 | h1426
                                · rcases p1424_3 (m.d 0 2) (by simp) with h1427 | h1427
                                  · linarith only [h0, h1427, hlam]
                                  · rcases p1424_3 (m.d 0 3) (by simp) with h1429 | h1429
                                    · linarith only [h1, h1429, hlam]
                                    · linarith only [h1429, h4, hlam]
                                · linarith only [h0, h1426, hlam]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                rcases p1424_3 (m.d 0 1) (by simp) with h1433 | h1433
                                · rcases p1424_3 (m.d 0 2) (by simp) with h1434 | h1434
                                  · linarith only [h0, h1434, hlam]
                                  · rcases p1424_3 (m.d 0 3) (by simp) with h1436 | h1436
                                    · linarith only [h1, h1436, hlam]
                                    · rcases p1424_3 (m.d 0 4) (by simp) with h1438 | h1438
                                      · linarith only [h1438, h2, hlam]
                                      · rcases p1424_3 (m.d 0 5) (by simp) with h1440 | h1440
                                        · linarith only [h1440, h3, hlam]
                                        · linarith only [h1440, h901, hlam]
                                · linarith only [h1, h1433, hlam]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                rcases p1424_3 (m.d 0 1) (by simp) with h1444 | h1444
                                · rcases p1424_3 (m.d 0 2) (by simp) with h1445 | h1445
                                  · linarith only [h0, h1445, hlam]
                                  · rcases p1424_3 (m.d 0 3) (by simp) with h1447 | h1447
                                    · linarith only [h1, h1447, hlam]
                                    · linarith only [h1447, h900, hlam]
                                · linarith only [h1444, h2, hlam]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1424_1, u5ehi1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h0, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h4, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h740, hlam, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h898, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h1, hlam, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h0, h1370, h901, hc12, hc23, hlam, hphi, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h0, h1370, h740, h901, hc12, hc23, hlam, hphi, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h901, hlam, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h2, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h0, h1371, h740, hc12, hc45, hlam, hphi, ht23, ht34, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h900, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h1356, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h3, hlam, p1424_0]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h0, h1370, h901, hc12, hc23, hlam, hphi, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h1, h1364, h1370, h901, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [h1360, h1370, h2, h901, hc12, hc23, hlam, hphi, p1424_1]
                              · have p1424_0 := h1424c.1
                                have p1424_1 := h1424c.2.1
                                have p1424_2 := h1424c.2.2.1
                                have p1424_3 := h1424c.2.2.2
                                linarith only [hlam, p1424_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1472 | h1472
                          · linarith only [h1356, h1369, h1370, h1472, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1474 | h1474
                            · linarith only [h1, h1364, h1472, h1474, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                            · rcases h0bigk with h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1478 | h1478
                                · rcases p1476_3 (m.d 0 2) (by simp) with h1479 | h1479
                                  · linarith only [h0, h1479, hlam]
                                  · rcases p1476_3 (m.d 0 3) (by simp) with h1481 | h1481
                                    · linarith only [h1, h1481, hlam]
                                    · linarith only [h1481, h4, hlam]
                                · linarith only [h0, h1478, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1485 | h1485
                                · rcases p1476_3 (m.d 0 2) (by simp) with h1486 | h1486
                                  · linarith only [h0, h1486, hlam]
                                  · rcases p1476_3 (m.d 0 3) (by simp) with h1488 | h1488
                                    · linarith only [h1, h1488, hlam]
                                    · rcases p1476_3 (m.d 0 4) (by simp) with h1490 | h1490
                                      · linarith only [h1490, h2, hlam]
                                      · rcases p1476_3 (m.d 0 5) (by simp) with h1492 | h1492
                                        · linarith only [h1492, h3, hlam]
                                        · linarith only [h1492, h901, hlam]
                                · linarith only [h1, h1485, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1496 | h1496
                                · rcases p1476_3 (m.d 0 2) (by simp) with h1497 | h1497
                                  · linarith only [h0, h1497, hlam]
                                  · rcases p1476_3 (m.d 0 3) (by simp) with h1499 | h1499
                                    · linarith only [h1, h1499, hlam]
                                    · linarith only [h1499, h900, hlam]
                                · linarith only [h1496, h2, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1476_1, u5ehi1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h4, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h740, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h898, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1370, h1474, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1370, h1474, h4, h740, hc12, hc45, hlam, hphi, ht23, ht34, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h901, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h2, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1370, h1474, h4, h900, hc12, hc45, hlam, hphi, ht23, ht34, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h900, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1356, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h3, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1520 | h1520
                                · rcases p1476_3 (m.d 0 2) (by simp) with h1521 | h1521
                                  · linarith only [h1521, h898, hlam]
                                  · rcases p1476_3 (m.d 0 3) (by simp) with h1523 | h1523
                                    · linarith only [h1523, h901, hlam]
                                    · linarith only [h1523, h4, hlam]
                                · linarith only [h0, h1520, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1, h1364, h1474, h901, hc34, hc45, hlam, hphi, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1528 | h1528
                                · rcases p1476_3 (m.d 0 2) (by simp) with h1529 | h1529
                                  · linarith only [h1529, h898, hlam]
                                  · rcases p1476_3 (m.d 0 3) (by simp) with h1531 | h1531
                                    · linarith only [h1531, h901, hlam]
                                    · linarith only [h1531, h900, hlam]
                                · linarith only [h1528, h2, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                      · linarith only [h0, h1, h1364, h1369, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1364, h900, h901, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1538 | h1538
      · linarith only [h1538, h900, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1540 | h1540
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1541 | h1541
          · linarith only [h0, h1541, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1543 | h1543
            · linarith only [h0, h1540, h1543, h740, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1545 | h1545
              · linarith only [h0, h1545, h898, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1547 | h1547
                · linarith only [h1, h1547, h900, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1549 | h1549
                  · linarith only [h1, h1549, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1551 | h1551
                    · linarith only [h1551, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1553 | h1553
                      · linarith only [h1540, h1551, h1553, h900, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1555 | h1555
                        · linarith only [h1538, h1553, h1555, hc03, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1557 | h1557
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1558 | h1558
                            · rcases h0bigk with h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                rcases p1559_3 (m.d 0 1) (by simp) with h1561 | h1561
                                · rcases p1559_3 (m.d 0 2) (by simp) with h1562 | h1562
                                  · linarith only [h0, h1562, hlam]
                                  · rcases p1559_3 (m.d 0 3) (by simp) with h1564 | h1564
                                    · linarith only [h1, h1564, hlam]
                                    · linarith only [h1564, h4, hlam]
                                · linarith only [h0, h1561, hlam]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                rcases p1559_3 (m.d 0 1) (by simp) with h1568 | h1568
                                · rcases p1559_3 (m.d 0 2) (by simp) with h1569 | h1569
                                  · linarith only [h0, h1569, hlam]
                                  · rcases p1559_3 (m.d 0 3) (by simp) with h1571 | h1571
                                    · linarith only [h1, h1571, hlam]
                                    · rcases p1559_3 (m.d 0 4) (by simp) with h1573 | h1573
                                      · linarith only [h1573, h2, hlam]
                                      · linarith only [h1573, h900, hlam]
                                · linarith only [h1, h1568, hlam]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h1540, h1551, hc01, hlam, hphi, ht0b, ht5b, p1559_1, u5ehi1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1559_1, u5ehi0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h0, hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h4, hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h740, hlam, p1559_1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h898, hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h1, hlam, p1559_1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h0, h1555, h1558, h4, hc12, hc34, hlam, hphi, ht23, p1559_1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h900, hlam, p1559_1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h1538, hlam, p1559_1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h2, hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                rcases p1559_3 (m.d 0 1) (by simp) with h1590 | h1590
                                · rcases p1559_3 (m.d 0 2) (by simp) with h1591 | h1591
                                  · linarith only [h1591, h740, hlam]
                                  · rcases p1559_3 (m.d 0 3) (by simp) with h1593 | h1593
                                    · linarith only [h1593, h900, hlam]
                                    · linarith only [h1593, h4, hlam]
                                · linarith only [h0, h1590, hlam]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                rcases p1559_3 (m.d 0 1) (by simp) with h1597 | h1597
                                · rcases p1559_3 (m.d 0 2) (by simp) with h1598 | h1598
                                  · linarith only [h1598, h740, hlam]
                                  · rcases p1559_3 (m.d 0 3) (by simp) with h1600 | h1600
                                    · linarith only [h1600, h900, hlam]
                                    · rcases p1559_3 (m.d 0 4) (by simp) with h1602 | h1602
                                      · rcases p1559_3 (m.d 0 5) (by simp) with h1603 | h1603
                                        · linarith only [h1540, h1603, hlam]
                                        · linarith only [h1538, h1603, hlam]
                                      · linarith only [h1602, h900, hlam]
                                · linarith only [h1, h1597, hlam]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h1540, h1551, hc04, hlam, hphi, ht0b, ht5b, p1559_1, u5ehi1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h3, hlam, p1559_0]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                rcases p1559_3 (m.d 0 1) (by simp) with h1611 | h1611
                                · rcases p1559_3 (m.d 0 2) (by simp) with h1612 | h1612
                                  · linarith only [h1612, h898, hlam]
                                  · rcases p1559_3 (m.d 0 3) (by simp) with h1614 | h1614
                                    · linarith only [h1538, h1614, hlam]
                                    · linarith only [h1614, h4, hlam]
                                · linarith only [h0, h1611, hlam]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                rcases p1559_3 (m.d 0 1) (by simp) with h1618 | h1618
                                · rcases p1559_3 (m.d 0 2) (by simp) with h1619 | h1619
                                  · linarith only [h1619, h898, hlam]
                                  · rcases p1559_3 (m.d 0 3) (by simp) with h1621 | h1621
                                    · linarith only [h1538, h1621, hlam]
                                    · rcases p1559_3 (m.d 0 4) (by simp) with h1623 | h1623
                                      · rcases p1559_3 (m.d 0 5) (by simp) with h1624 | h1624
                                        · rcases h2bigk with h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1559_1, p1625_1]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h4, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h740, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h898, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h0, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1541, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1543, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1545, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1555, h1558, hc02, hc34, hlam, hphi, ht23, p1625_1]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1555, h1558, hc12, hc34, hlam, hphi, ht23, p1625_1]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1553, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1555, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            rcases p1625_3 (m.d 0 2) (by simp) with h1641 | h1641
                                            · linarith only [h1641, hlam, p1625_0]
                                            · rcases p1625_3 (m.d 1 2) (by simp) with h1643 | h1643
                                              · linarith only [h1543, h1643, hlam]
                                              · rcases p1625_3 (m.d 2 3) (by simp) with h1645 | h1645
                                                · linarith only [h1553, h1645, hlam]
                                                · linarith only [h1645, h4, hlam]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            rcases p1625_3 (m.d 0 2) (by simp) with h1648 | h1648
                                            · linarith only [h1648, h740, hlam]
                                            · linarith only [h0, h1648, hlam]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h0, h1553, h4, hc12, hc34, hlam, hphi, ht23, p1625_1]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1625_1, u5ehi2]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            rcases p1625_3 (m.d 0 2) (by simp) with h1654 | h1654
                                            · linarith only [h1654, hlam, p1625_0]
                                            · rcases p1625_3 (m.d 1 2) (by simp) with h1656 | h1656
                                              · linarith only [h1545, h1656, hlam]
                                              · rcases p1625_3 (m.d 2 3) (by simp) with h1658 | h1658
                                                · linarith only [h1555, h1658, hlam]
                                                · linarith only [h1658, h4, hlam]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            rcases p1625_3 (m.d 0 2) (by simp) with h1661 | h1661
                                            · linarith only [h1661, h898, hlam]
                                            · linarith only [h0, h1661, hlam]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h0, h4, hc12, hc25, hlam, hphi, p1625_1]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [h1557, hlam, p1625_0]
                                          · have p1625_0 := h1625c.1
                                            have p1625_1 := h1625c.2.1
                                            have p1625_2 := h1625c.2.2.1
                                            have p1625_3 := h1625c.2.2.2
                                            linarith only [hlam, p1625_0]
                                        · linarith only [h1538, h1624, hlam]
                                      · linarith only [h1623, h900, hlam]
                                · linarith only [h1, h1618, hlam]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [h1540, hlam, p1559_1]
                              · have p1559_0 := h1559c.1
                                have p1559_1 := h1559c.2.1
                                have p1559_2 := h1559c.2.2.1
                                have p1559_3 := h1559c.2.2.2
                                linarith only [hlam, p1559_0]
                            · linarith only [h1540, h1553, h1558, h740, hlam]
                          · linarith only [h1540, h1557, h740, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1674 | h1674
          · linarith only [h0, h1674, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1676 | h1676
            · linarith only [h0, h1676, h740, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1678 | h1678
              · linarith only [h0, h1678, h4, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
                · linarith only [h1, h1680, h900, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1682 | h1682
                  · linarith only [h1, h1540, h1682, h900, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
                    · linarith only [h1684, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1686 | h1686
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1687 | h1687
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1688 | h1688
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1689 | h1689
                            · linarith only [h1686, h1689, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h0, h1686, h1688, h1689, h4, h900, hc12, hc23, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1692 | h1692
                            · linarith only [h0, h1688, h1692, h740, hc12, hc34, hlam, hphi, ht23]
                            · rcases h0bigk with h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                rcases p1694_3 (m.d 0 1) (by simp) with h1696 | h1696
                                · rcases p1694_3 (m.d 0 2) (by simp) with h1697 | h1697
                                  · linarith only [h0, h1697, hlam]
                                  · rcases p1694_3 (m.d 0 3) (by simp) with h1699 | h1699
                                    · linarith only [h1, h1699, hlam]
                                    · linarith only [h1699, h4, hlam]
                                · linarith only [h0, h1696, hlam]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                rcases p1694_3 (m.d 0 1) (by simp) with h1703 | h1703
                                · rcases p1694_3 (m.d 0 2) (by simp) with h1704 | h1704
                                  · linarith only [h0, h1704, hlam]
                                  · rcases p1694_3 (m.d 0 3) (by simp) with h1706 | h1706
                                    · linarith only [h1, h1706, hlam]
                                    · rcases p1694_3 (m.d 0 4) (by simp) with h1708 | h1708
                                      · linarith only [h1708, h2, hlam]
                                      · linarith only [h1708, h900, hlam]
                                · linarith only [h1, h1703, hlam]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                rcases p1694_3 (m.d 0 1) (by simp) with h1712 | h1712
                                · rcases p1694_3 (m.d 0 2) (by simp) with h1713 | h1713
                                  · linarith only [h0, h1713, hlam]
                                  · rcases p1694_3 (m.d 0 3) (by simp) with h1715 | h1715
                                    · linarith only [h1, h1715, hlam]
                                    · rcases p1694_3 (m.d 0 4) (by simp) with h1717 | h1717
                                      · linarith only [h1717, h2, hlam]
                                      · rcases p1694_3 (m.d 0 5) (by simp) with h1719 | h1719
                                        · linarith only [h1719, h3, hlam]
                                        · linarith only [h1540, h1719, hlam]
                                · linarith only [h1712, h2, hlam]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1694_1, u5ehi1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h0, hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h4, hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h740, hlam, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h898, hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h1, hlam, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h0, h1686, h900, hc12, hc24, hlam, hphi, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h900, hlam, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h1538, hlam, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h2, hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h0, h1686, h1688, h900, hc12, hc45, hlam, hphi, ht23, ht34, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h1686, h1688, h900, hc03, hc45, hlam, hphi, ht34, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h1540, hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h3, hlam, p1694_0]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h0, h1538, h1687, hc12, hc23, hlam, hphi, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h1, h1538, h1674, h1687, hc12, hc23, hlam, hphi, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [h0, h1538, h1687, h740, hc12, hc23, hlam, hphi, p1694_1]
                              · have p1694_0 := h1694c.1
                                have p1694_1 := h1694c.2.1
                                have p1694_2 := h1694c.2.2.1
                                have p1694_3 := h1694c.2.2.2
                                linarith only [hlam, p1694_0]
                        · linarith only [h1, h1674, h1686, h1687, h900, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1745 | h1745
                        · linarith only [h1686, h1745, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1747 | h1747
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1748 | h1748
                            · rcases h0bigk with h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                rcases p1749_3 (m.d 0 1) (by simp) with h1751 | h1751
                                · rcases p1749_3 (m.d 0 2) (by simp) with h1752 | h1752
                                  · linarith only [h0, h1752, hlam]
                                  · rcases p1749_3 (m.d 0 3) (by simp) with h1754 | h1754
                                    · linarith only [h1, h1754, hlam]
                                    · linarith only [h1754, h4, hlam]
                                · linarith only [h0, h1751, hlam]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                rcases p1749_3 (m.d 0 1) (by simp) with h1758 | h1758
                                · rcases p1749_3 (m.d 0 2) (by simp) with h1759 | h1759
                                  · linarith only [h0, h1759, hlam]
                                  · rcases p1749_3 (m.d 0 3) (by simp) with h1761 | h1761
                                    · linarith only [h1, h1761, hlam]
                                    · rcases p1749_3 (m.d 0 4) (by simp) with h1763 | h1763
                                      · linarith only [h1763, h2, hlam]
                                      · linarith only [h1763, h900, hlam]
                                · linarith only [h1, h1758, hlam]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                rcases p1749_3 (m.d 0 1) (by simp) with h1767 | h1767
                                · rcases p1749_3 (m.d 0 2) (by simp) with h1768 | h1768
                                  · linarith only [h0, h1768, hlam]
                                  · rcases p1749_3 (m.d 0 3) (by simp) with h1770 | h1770
                                    · linarith only [h1, h1770, hlam]
                                    · rcases p1749_3 (m.d 0 4) (by simp) with h1772 | h1772
                                      · linarith only [h1772, h2, hlam]
                                      · rcases p1749_3 (m.d 0 5) (by simp) with h1774 | h1774
                                        · linarith only [h1774, h3, hlam]
                                        · linarith only [h1540, h1774, hlam]
                                · linarith only [h1767, h2, hlam]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1749_1, u5ehi0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h0, hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h4, hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h740, hlam, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h898, hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h1, hlam, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h0, h1745, h1748, h4, hc12, hc34, hlam, hphi, ht23, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h900, hlam, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h1538, hlam, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h2, hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h0, h1540, h1686, h1747, hc12, hc34, hlam, hphi, ht23, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h1540, h1686, h1747, hc03, hc34, hlam, hphi, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h1540, hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h3, hlam, p1749_0]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h0, h1540, h1686, h1747, hc12, hc34, hlam, hphi, ht23, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h1, h1540, h1674, h1686, h1747, hc12, hc34, hlam, hphi, ht23, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [h1540, h1674, h1680, h1686, h1747, h2, hc12, hc34, hlam, hphi, ht23, p1749_1]
                              · have p1749_0 := h1749c.1
                                have p1749_1 := h1749c.2.1
                                have p1749_2 := h1749c.2.2.1
                                have p1749_3 := h1749c.2.2.2
                                linarith only [hlam, p1749_0]
                            · linarith only [h1686, h1747, h1748, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1800 | h1800
                            · linarith only [h0, h1686, h1747, h1800, h4, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1686, h1800, h4, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
