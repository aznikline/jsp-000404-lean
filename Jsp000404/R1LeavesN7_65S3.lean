import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S2

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_R_L_I_L_R_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h867 | h867
  · linarith only [h0, h867, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h869 | h869
    · linarith only [h0, h869, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h871 | h871
      · linarith only [h0, h871, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h873 | h873
        · rcases m.htr 0 2 4 (by decide) (by decide) with h874 | h874
          · rcases m.htr 0 2 5 (by decide) (by decide) with h875 | h875
            · rcases m.htr 0 3 4 (by decide) (by decide) with h876 | h876
              · rcases m.htr 0 3 5 (by decide) (by decide) with h877 | h877
                · rcases m.htr 0 4 5 (by decide) (by decide) with h878 | h878
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h880 | h880
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h881 | h881
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h882 | h882
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h883 | h883
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h884 | h884
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h885 | h885
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h886 | h886
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h887 | h887
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h888 | h888
                                      · linarith only [h873, h885, h888, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                      · linarith only [h0, h874, h887, h888, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h891 | h891
                                      · linarith only [h885, h887, h891, hlam]
                                      · rcases h2bigk with h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c | h893c
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h0, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h0, h886, hc12, hlam, hphi, ht01, ht0b, ht5b, p893_1, u5ehi3]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          rcases p893_3 (m.d 0 2) (by simp) with h897 | h897
                                          · rcases p893_3 (m.d 1 2) (by simp) with h898 | h898
                                            · rcases p893_3 (m.d 2 3) (by simp) with h899 | h899
                                              · linarith only [h873, h899, hlam]
                                              · linarith only [h885, h899, hlam]
                                            · linarith only [h880, h898, hlam]
                                          · linarith only [h897, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          rcases p893_3 (m.d 0 2) (by simp) with h904 | h904
                                          · rcases p893_3 (m.d 1 2) (by simp) with h905 | h905
                                            · rcases p893_3 (m.d 2 3) (by simp) with h906 | h906
                                              · linarith only [h873, h906, hlam]
                                              · linarith only [h886, h906, hlam]
                                            · linarith only [h881, h905, hlam]
                                          · linarith only [h904, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, p893_1, u1ehi0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h886, h891, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p893_1, u4ehi3]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          rcases p893_3 (m.d 0 2) (by simp) with h914 | h914
                                          · linarith only [h0, h914, hlam]
                                          · linarith only [h874, h914, hlam]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          rcases p893_3 (m.d 0 2) (by simp) with h917 | h917
                                          · linarith only [h0, h917, hlam]
                                          · linarith only [h875, h917, hlam]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h873, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h879, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h873, h885, hc02, hlam, hphi, ht0b, ht45, ht5b, p893_1, u4ehi3]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h0, h873, h886, h891, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p893_1, u4ehi3]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h874, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h880, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h885, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h887, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h875, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h881, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h886, hlam, p893_0]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [h0, h875, h885, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p893_1, u4ehi3]
                                        · have p893_0 := h893c.1
                                          have p893_1 := h893c.2.1
                                          have p893_2 := h893c.2.2.1
                                          have p893_3 := h893c.2.2.2
                                          linarith only [hlam, p893_0]
                                  · linarith only [h867, h877, h879, h885, h886, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h936 | h936
                                  · linarith only [h867, h876, h879, h885, h936, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h938 | h938
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h939 | h939
                                      · rcases h2bigk with h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h0, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          rcases p940_3 (m.d 0 2) (by simp) with h943 | h943
                                          · rcases p940_3 (m.d 1 2) (by simp) with h944 | h944
                                            · rcases p940_3 (m.d 2 3) (by simp) with h945 | h945
                                              · linarith only [h945, hlam, p940_0]
                                              · rcases p940_3 (m.d 2 4) (by simp) with h947 | h947
                                                · linarith only [h874, h947, hlam]
                                                · linarith only [h885, h947, hlam]
                                            · linarith only [h879, h944, hlam]
                                          · linarith only [h943, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h0, h938, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u4ehi4]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          rcases p940_3 (m.d 0 2) (by simp) with h953 | h953
                                          · rcases p940_3 (m.d 1 2) (by simp) with h954 | h954
                                            · rcases p940_3 (m.d 2 3) (by simp) with h955 | h955
                                              · linarith only [h873, h955, hlam]
                                              · rcases p940_3 (m.d 2 4) (by simp) with h957 | h957
                                                · linarith only [h874, h957, hlam]
                                                · linarith only [h938, h957, hlam]
                                            · linarith only [h881, h954, hlam]
                                          · linarith only [h953, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, p940_1, u1ehi0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          rcases p940_3 (m.d 0 2) (by simp) with h964 | h964
                                          · linarith only [h0, h964, hlam]
                                          · linarith only [h873, h964, hlam]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h938, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u4ehi4]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          rcases p940_3 (m.d 0 2) (by simp) with h968 | h968
                                          · linarith only [h0, h968, hlam]
                                          · linarith only [h875, h968, hlam]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h873, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h879, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h885, hlam, p940_1]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h936, hlam, p940_1]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h874, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h880, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          rcases p940_3 (m.d 0 2) (by simp) with h978 | h978
                                          · rcases p940_3 (m.d 1 2) (by simp) with h979 | h979
                                            · rcases p940_3 (m.d 2 3) (by simp) with h980 | h980
                                              · linarith only [h885, h980, hlam]
                                              · rcases p940_3 (m.d 2 4) (by simp) with h982 | h982
                                                · rcases p940_3 (m.d 2 5) (by simp) with h983 | h983
                                                  · linarith only [h938, h983, hlam]
                                                  · linarith only [h936, h983, hlam]
                                                · linarith only [h885, h982, hlam]
                                            · linarith only [h879, h979, hlam]
                                          · linarith only [h873, h978, hlam]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h867, h876, h879, h885, h938, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u4ehi4]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h875, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h881, hlam, p940_0]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          rcases p940_3 (m.d 0 2) (by simp) with h993 | h993
                                          · rcases p940_3 (m.d 1 2) (by simp) with h994 | h994
                                            · rcases p940_3 (m.d 2 3) (by simp) with h995 | h995
                                              · linarith only [h936, h995, hlam]
                                              · rcases p940_3 (m.d 2 4) (by simp) with h997 | h997
                                                · rcases p940_3 (m.d 2 5) (by simp) with h998 | h998
                                                  · rcases h5bigk with h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c | h999c
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [hlam, p999_0]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h871, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p940_1, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h871, h879, h882, h884, h936, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p940_1, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      rcases p999_3 (m.d 0 5) (by simp) with h1004 | h1004
                                                      · rcases p999_3 (m.d 1 5) (by simp) with h1005 | h1005
                                                        · rcases p999_3 (m.d 2 5) (by simp) with h1006 | h1006
                                                          · linarith only [h1006, h875, hlam]
                                                          · linarith only [h1006, h938, hlam]
                                                        · linarith only [h1005, h884, hlam]
                                                      · linarith only [h1004, h878, hlam]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h871, h879, h882, h884, hc12, hlam, hphi, p999_1, u1ehi0]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [hlam, p999_0]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h879, h882, h884, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p940_1, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h879, h882, h884, h936, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p940_1, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      rcases p999_3 (m.d 0 5) (by simp) with h1015 | h1015
                                                      · linarith only [h1015, h871, hlam]
                                                      · linarith only [h1015, h878, hlam]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h875, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h881, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [hlam, p999_0]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h936, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h876, h885, h938, hc03, hlam, hphi, ht0b, ht45, ht5b, p999_1, u4ehi4]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h877, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h883, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h877, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p940_1, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [hlam, p999_0]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h867, h876, h879, h939, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p999_1, u4ehi4]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h878, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h884, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h938, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [h939, hlam, p999_1]
                                                    · have p999_0 := h999c.1
                                                      have p999_1 := h999c.2.1
                                                      have p999_2 := h999c.2.2.1
                                                      have p999_3 := h999c.2.2.2
                                                      linarith only [hlam, p999_0]
                                                  · linarith only [h936, h998, hlam]
                                                · linarith only [h885, h997, hlam]
                                            · linarith only [h879, h994, hlam]
                                          · linarith only [h873, h993, hlam]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [h938, hlam, p940_1]
                                        · have p940_0 := h940c.1
                                          have p940_1 := h940c.2.1
                                          have p940_2 := h940c.2.2.1
                                          have p940_3 := h940c.2.2.2
                                          linarith only [hlam, p940_0]
                                      · linarith only [h885, h938, h939, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1040 | h1040
                                      · linarith only [h1040, h867, h876, h879, h938, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                      · rcases h2bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h0, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h1040, h873, h876, h878, h885, hlam, p1042_2]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          rcases p1042_3 (m.d 0 2) (by simp) with h1046 | h1046
                                          · rcases p1042_3 (m.d 1 2) (by simp) with h1047 | h1047
                                            · rcases p1042_3 (m.d 2 3) (by simp) with h1048 | h1048
                                              · linarith only [h1048, h873, hlam]
                                              · rcases p1042_3 (m.d 2 4) (by simp) with h1050 | h1050
                                                · linarith only [h1050, hlam, p1042_0]
                                                · rcases p1042_3 (m.d 2 5) (by simp) with h1052 | h1052
                                                  · linarith only [h1052, h875, hlam]
                                                  · linarith only [h1052, h938, hlam]
                                            · linarith only [h1047, h880, hlam]
                                          · linarith only [h1046, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          rcases p1042_3 (m.d 0 2) (by simp) with h1057 | h1057
                                          · rcases p1042_3 (m.d 1 2) (by simp) with h1058 | h1058
                                            · rcases p1042_3 (m.d 2 3) (by simp) with h1059 | h1059
                                              · linarith only [h1059, h873, hlam]
                                              · rcases p1042_3 (m.d 2 4) (by simp) with h1061 | h1061
                                                · linarith only [h1061, h874, hlam]
                                                · rcases p1042_3 (m.d 2 5) (by simp) with h1063 | h1063
                                                  · linarith only [h1063, hlam, p1042_0]
                                                  · rcases h5bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [hlam, p1065_0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h871, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      rcases p1065_3 (m.d 0 5) (by simp) with h1068 | h1068
                                                      · rcases p1065_3 (m.d 1 5) (by simp) with h1069 | h1069
                                                        · rcases p1065_3 (m.d 2 5) (by simp) with h1070 | h1070
                                                          · linarith only [h1070, h875, hlam]
                                                          · rcases p1065_3 (m.d 3 5) (by simp) with h1072 | h1072
                                                            · linarith only [h1072, h877, hlam]
                                                            · linarith only [h1072, h936, hlam]
                                                        · linarith only [h1069, h881, hlam]
                                                      · linarith only [h1068, h875, hlam]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      rcases p1065_3 (m.d 0 5) (by simp) with h1077 | h1077
                                                      · rcases p1065_3 (m.d 1 5) (by simp) with h1078 | h1078
                                                        · rcases p1065_3 (m.d 2 5) (by simp) with h1079 | h1079
                                                          · linarith only [h1079, h875, hlam]
                                                          · rcases p1065_3 (m.d 3 5) (by simp) with h1081 | h1081
                                                            · linarith only [h1081, h877, hlam]
                                                            · rcases p1065_3 (m.d 4 5) (by simp) with h1083 | h1083
                                                              · linarith only [h1083, h878, hlam]
                                                              · linarith only [h1040, h1083, hlam]
                                                        · linarith only [h1078, h883, hlam]
                                                      · linarith only [h1077, h877, hlam]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h1040, h873, h876, h878, h885, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h871, h879, h882, h884, hc12, hlam, hphi, p1065_1, u1ehi0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [hlam, p1065_0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      rcases p1065_3 (m.d 0 5) (by simp) with h1091 | h1091
                                                      · linarith only [h1091, h871, hlam]
                                                      · linarith only [h1091, h875, hlam]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      rcases p1065_3 (m.d 0 5) (by simp) with h1094 | h1094
                                                      · linarith only [h1094, h871, hlam]
                                                      · linarith only [h1094, h877, hlam]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h1040, h879, h882, h884, h885, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h875, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h881, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [hlam, p1065_0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h936, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h938, hlam, p1065_0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h877, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h883, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h0, h873, h877, h938, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1065_1, u4ehi2]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [hlam, p1065_0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h1040, hlam, p1065_0]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h878, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h884, hlam, p1065_1]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h938, hc45, hlam, hphi, p1065_1, u4ehi2]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [h0, h873, h876, h878, hc12, hlam, hphi, ht01, ht0b, ht5b, p1065_1, u5ehi3]
                                                    · have p1065_0 := h1065c.1
                                                      have p1065_1 := h1065c.2.1
                                                      have p1065_2 := h1065c.2.2.1
                                                      have p1065_3 := h1065c.2.2.2
                                                      linarith only [hlam, p1065_0]
                                            · linarith only [h1058, h881, hlam]
                                          · linarith only [h1057, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h873, h876, h878, hc12, hlam, hphi, ht01, ht0b, ht5b, p1042_1, u5ehi4]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h0, h1040, h873, h876, h878, h885, hlam, p1042_2]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          rcases p1042_3 (m.d 0 2) (by simp) with h1118 | h1118
                                          · linarith only [h0, h1118, hlam]
                                          · linarith only [h1118, h874, hlam]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          rcases p1042_3 (m.d 0 2) (by simp) with h1121 | h1121
                                          · linarith only [h0, h1121, hlam]
                                          · linarith only [h1121, h875, hlam]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h873, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h879, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h885, hlam, p1042_1]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h936, hlam, p1042_1]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h874, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h880, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h0, h1040, h873, h876, h878, h885, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1042_1]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h938, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h875, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h881, hlam, p1042_0]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          rcases p1042_3 (m.d 0 2) (by simp) with h1136 | h1136
                                          · rcases p1042_3 (m.d 1 2) (by simp) with h1137 | h1137
                                            · rcases p1042_3 (m.d 2 3) (by simp) with h1138 | h1138
                                              · linarith only [h1138, h936, hlam]
                                              · rcases p1042_3 (m.d 2 4) (by simp) with h1140 | h1140
                                                · linarith only [h1140, h938, hlam]
                                                · linarith only [h1140, h885, hlam]
                                            · linarith only [h1137, h879, hlam]
                                          · linarith only [h1136, h873, hlam]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [h0, h875, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1042_1, u4ehi2]
                                        · have p1042_0 := h1042c.1
                                          have p1042_1 := h1042c.2.1
                                          have p1042_2 := h1042c.2.2.1
                                          have p1042_3 := h1042c.2.2.2
                                          linarith only [hlam, p1042_0]
                              · linarith only [h0, h873, h876, h878, h884, hc12, hlam, hphi, u1ehi3]
                            · linarith only [h867, h883, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h867, h882, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h875, h881, hlam]
                      · linarith only [h0, h880, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h879, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1153 | h1153
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1154 | h1154
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1155 | h1155
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1156 | h1156
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1157 | h1157
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1158 | h1158
                              · linarith only [h1156, h1158, h869, h878, hc13, hlam, hphi, u1ehi0]
                              · linarith only [h1158, h869, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                            · linarith only [h0, h1157, h873, h877, hc12, hlam, hphi, u1ehi2]
                          · linarith only [h1156, h867, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h1155, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h0, h1154, h874, hlam]
                    · linarith only [h0, h1153, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1166 | h1166
                  · linarith only [h1166, h876, h877, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1168 | h1168
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1169 | h1169
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1170 | h1170
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1171 | h1171
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1172 | h1172
                            · linarith only [h1172, h867, h877, hc13, hlam, hphi, u1ehi0]
                            · linarith only [h1172, h867, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                          · linarith only [h1171, h867, h876, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                        · linarith only [h0, h1170, h875, hlam]
                      · linarith only [h0, h1166, h1169, h874, h875, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h0, h1168, h873, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1179 | h1179
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1180 | h1180
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1181 | h1181
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1182 | h1182
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1183 | h1183
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1184 | h1184
                          · linarith only [h1179, h1184, h876, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h1184, h867, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h1183, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h1181, h1182, h867, h874, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h0, h1181, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1179, h1180, h876, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1191 | h1191
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1192 | h1192
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1193 | h1193
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1194 | h1194
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                          · linarith only [h1192, h1195, h867, h876, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h1195, h867, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h1194, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h1192, h1193, h867, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1192, h873, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1201 | h1201
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1202 | h1202
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1203 | h1203
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1204 | h1204
                          · linarith only [h1204, h867, h876, hc13, hlam, hphi, u1ehi0]
                          · linarith only [h1204, h867, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h0, h1203, h875, hlam]
                      · linarith only [h0, h1202, h874, hlam]
                    · linarith only [h0, h1201, h873, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1210 | h1210
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1211 | h1211
                · linarith only [h1211, h873, h875, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1213 | h1213
                  · linarith only [h1210, h1213, h873, h875, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1215 | h1215
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1216 | h1216
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1217 | h1217
                        · linarith only [h1217, h874, h875, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1217, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h1215, h1216, h867, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1215, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1222 | h1222
                · linarith only [h1210, h1222, h874, h875, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1224 | h1224
                  · linarith only [h1224, h874, h875, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1226 | h1226
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1227 | h1227
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1228 | h1228
                        · linarith only [h1228, h874, h875, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1228, hc25, hlam, hphi, ht12, u1ehi0]
                      · linarith only [h1226, h1227, h867, h874, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h0, h1226, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1233 | h1233
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1234 | h1234
              · linarith only [h1234, h873, h874, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1238 | h1238
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1239 | h1239
                      · linarith only [h1236, h1239, h873, h874, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h1239, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1238, h873, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h1236, h1237, h873, h874, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1245 | h1245
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1246 | h1246
                      · linarith only [h0, h1246, h874, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1246, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1245, h873, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h1233, h1244, h874, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1251 | h1251
              · linarith only [h1251, h873, h874, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1253 | h1253
                · linarith only [h1233, h1253, h873, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1255 | h1255
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1256 | h1256
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1257 | h1257
                      · linarith only [h0, h1257, h874, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1257, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1256, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1261 | h1261
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1262 | h1262
                      · linarith only [h1262, h867, h873, h874, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1262, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1261, h873, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1266 | h1266
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1267 | h1267
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1268 | h1268
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1269 | h1269
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1270 | h1270
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1271 | h1271
                    · linarith only [h1266, h1270, h1271, h873, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1271, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
                    · linarith only [h1267, h1274, h873, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h1274, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h1267, h1269, h873, hlam]
              · linarith only [h1266, h1268, h873, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1279 | h1279
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1280 | h1280
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1281 | h1281
                  · linarith only [h1266, h1267, h1281, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1283 | h1283
                    · linarith only [h0, h1283, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1283, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1286 | h1286
                  · linarith only [h1266, h1280, h1286, h873, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
                    · linarith only [h0, h1288, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1288, hc23, hlam, hphi, ht12, u1ehi0]
              · linarith only [h1266, h1279, h873, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1292 | h1292
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1293 | h1293
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1294 | h1294
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1295 | h1295
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1296 | h1296
                    · linarith only [h1292, h1296, h873, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h1296, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1266, h1292, h1295, hlam]
                · linarith only [h1266, h1292, h1293, h1294, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1301 | h1301
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1302 | h1302
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1303 | h1303
                    · linarith only [h1292, h1303, h873, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h1303, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1292, h1293, h1302, h873, hlam]
                · linarith only [h1292, h1301, h873, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1308 | h1308
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1309 | h1309
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1310 | h1310
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1311 | h1311
                    · linarith only [h0, h1311, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1311, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1314 | h1314
                    · linarith only [h0, h1314, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1314, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1317 | h1317
                  · linarith only [h1308, h1309, h1317, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1319 | h1319
                    · linarith only [h0, h1319, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1319, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1322 | h1322
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1323 | h1323
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1324 | h1324
                    · linarith only [h0, h1324, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1324, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1308, h1322, h1323, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1328 | h1328
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1329 | h1329
                    · linarith only [h0, h1329, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1329, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1332 | h1332
                    · linarith only [h0, h1332, h873, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1332, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_12_14_25_L_R_L_I_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_R_L_I_L_R_M_IR_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_R_L_I_L_R_M_IR_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
