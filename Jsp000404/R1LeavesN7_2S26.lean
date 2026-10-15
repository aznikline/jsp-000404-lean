import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S25

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h14396 := hg14396
  rcases m.htr 0 2 3 (by decide) (by decide) with h15886 | h15886
  · rcases m.htr 0 2 4 (by decide) (by decide) with h15887 | h15887
    · rcases m.htr 0 2 5 (by decide) (by decide) with h15888 | h15888
      · rcases m.htr 0 3 4 (by decide) (by decide) with h15889 | h15889
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15890 | h15890
          · linarith only [h14396, h14398, h15890, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15892 | h15892
            · linarith only [h14396, h14398, h15889, h15892, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15894 | h15894
              · rcases m.htr 1 2 4 (by decide) (by decide) with h15895 | h15895
                · rcases m.htr 1 2 5 (by decide) (by decide) with h15896 | h15896
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15897 | h15897
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h15898 | h15898
                      · linarith only [h14396, h14398, h15890, h15896, h15898, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15900 | h15900
                        · linarith only [h14397, h14398, h15892, h15900, hlam]
                        · linarith only [h14396, h14398, h15897, h15900, hc34, hc45, hlam, hphi]
                    · linarith only [h15889, h15890, h15894, h15897, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h14397, h15888, h15896, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h15887, h15895, hlam]
              · linarith only [h0, h15886, h15894, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15907 | h15907
          · linarith only [h14397, h14398, h15889, h15907, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15909 | h15909
            · linarith only [h14397, h14398, h15909, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15911 | h15911
              · rcases m.htr 1 2 4 (by decide) (by decide) with h15912 | h15912
                · rcases m.htr 1 2 5 (by decide) (by decide) with h15913 | h15913
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15914 | h15914
                    · linarith only [h14396, h14398, h15889, h15913, h15914, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h15916 | h15916
                      · linarith only [h14396, h14398, h15907, h15916, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15918 | h15918
                        · linarith only [h14397, h14398, h15889, h15909, h15916, h15918, hc03, hc35, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15920 | h15920
                          · linarith only [h14396, h14398, h15911, h15918, h15920, hc34, hc45, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h15922 | h15922
                            · linarith only [h14397, h14398, h15907, h15911, h15914, h15918, h15922, hc03, hc45, hlam, hphi, ht34]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h15924 | h15924
                              · linarith only [h14397, h14398, h15912, h15918, h15924, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15926 | h15926
                                · linarith only [h14396, h14398, h15911, h15918, h15926, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c | h15928c
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h0, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14396, h14398, h15911, h15916, hc23, hc35, hlam, hphi, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14398, h15916, h15926, hc04, hc45, hlam, hphi, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14398, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    rcases p15928_3 (m.d 0 1) (by simp) with h15934 | h15934
                                    · linarith only [h0, h15934, hlam]
                                    · rcases p15928_3 (m.d 0 2) (by simp) with h15936 | h15936
                                      · rcases p15928_3 (m.d 0 3) (by simp) with h15937 | h15937
                                        · linarith only [h15886, h15937, hlam]
                                        · rcases p15928_3 (m.d 0 4) (by simp) with h15939 | h15939
                                          · linarith only [h15887, h15939, hlam]
                                          · rcases p15928_3 (m.d 0 5) (by simp) with h15941 | h15941
                                            · linarith only [h15888, h15941, hlam]
                                            · linarith only [h14398, h15941, hlam]
                                      · linarith only [h0, h15936, hlam]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    rcases p15928_3 (m.d 0 1) (by simp) with h15946 | h15946
                                    · linarith only [h0, h15946, hlam]
                                    · linarith only [h14396, h15946, hlam]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    rcases p15928_3 (m.d 0 1) (by simp) with h15949 | h15949
                                    · linarith only [h0, h15949, hlam]
                                    · linarith only [h14397, h15949, hlam]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    rcases p15928_3 (m.d 0 1) (by simp) with h15952 | h15952
                                    · linarith only [h0, h15952, hlam]
                                    · rcases p15928_3 (m.d 0 2) (by simp) with h15954 | h15954
                                      · rcases p15928_3 (m.d 0 3) (by simp) with h15955 | h15955
                                        · linarith only [h15886, h15955, hlam]
                                        · rcases p15928_3 (m.d 0 4) (by simp) with h15957 | h15957
                                          · linarith only [h15887, h15957, hlam]
                                          · rcases p15928_3 (m.d 0 5) (by simp) with h15959 | h15959
                                            · linarith only [h15888, h15959, hlam]
                                            · rcases h2bigk with h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c | h15961c
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h0, hlam, p15961_1]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h14397, h14398, h15911, h15914, hlam, p15928_1, p15961_2]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h14397, h14398, h15912, hlam, p15928_1, p15961_2]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                rcases p15961_3 (m.d 0 2) (by simp) with h15966 | h15966
                                                · rcases p15961_3 (m.d 1 2) (by simp) with h15967 | h15967
                                                  · rcases p15961_3 (m.d 2 3) (by simp) with h15968 | h15968
                                                    · linarith only [h15886, h15968, hlam]
                                                    · rcases p15961_3 (m.d 2 4) (by simp) with h15970 | h15970
                                                      · linarith only [h15887, h15970, hlam]
                                                      · rcases p15961_3 (m.d 2 5) (by simp) with h15972 | h15972
                                                        · linarith only [h15972, hlam, p15961_0]
                                                        · rcases h3bigk with h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c | h15974c
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h14396, h14398, h15911, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15928_1, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h0, h14396, h14398, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15928_1, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15889, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15907, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h14396, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h0, h14396, h14398, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15928_1, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15914, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15916, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15886, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15911, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15920, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15922, hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15926, hc03, hc45, hlam, hphi, ht34, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15911, h15926, hc23, hc45, hlam, hphi, ht34, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15926, hc23, hc45, hlam, hphi, ht34, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [hlam, p15974_0]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15926, hlam, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h14396, h15911, h15926, hc23, hc45, hlam, hphi, ht34, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15911, h15926, hc23, hc45, hlam, hphi, ht34, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15926, hc23, hc45, hlam, hphi, ht34, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [h15926, hc34, hc45, hlam, hphi, p15974_1]
                                                          · have p15974_0 := h15974c.1
                                                            have p15974_1 := h15974c.2.1
                                                            have p15974_2 := h15974c.2.2.1
                                                            have p15974_3 := h15974c.2.2.2
                                                            linarith only [hlam, p15974_0]
                                                  · linarith only [h15913, h15967, hlam]
                                                · linarith only [h15966, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h14398, hc01, hc12, hlam, hphi, p15928_1, p15961_1]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h0, h14396, h14398, h15911, hlam, p15928_1, p15961_2]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h0, h14397, h14398, h15912, hlam, p15928_1, p15961_2]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                rcases p15961_3 (m.d 0 2) (by simp) with h16006 | h16006
                                                · linarith only [h0, h16006, hlam]
                                                · linarith only [h15888, h16006, hlam]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15886, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15911, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15920, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15922, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15887, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15912, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h14397, h14398, h15912, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15928_1, p15961_1]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15924, hlam, p15961_1]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15888, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h15913, hlam, p15961_0]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h0, h15888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15928_1, p15961_1]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [h0, h15888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15928_1, p15961_1]
                                              · have p15961_0 := h15961c.1
                                                have p15961_1 := h15961c.2.1
                                                have p15961_2 := h15961c.2.2.1
                                                have p15961_3 := h15961c.2.2.2
                                                linarith only [hlam, p15961_0]
                                      · linarith only [h15888, h15954, hlam]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14396, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h15886, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h15889, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h15907, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14397, hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h15887, hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14396, h14397, h14398, h15911, h15916, h15926, hc23, hc45, hlam, hphi, ht34, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h15909, hlam, p15928_0]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h14397, h14398, h15916, h15926, hc14, hc45, hlam, hphi, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [h15888, hlam, p15928_1]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    rcases p15928_3 (m.d 0 1) (by simp) with h16037 | h16037
                                    · linarith only [h14398, h16037, hlam]
                                    · linarith only [h14396, h16037, hlam]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    rcases p15928_3 (m.d 0 1) (by simp) with h16040 | h16040
                                    · linarith only [h14398, h16040, hlam]
                                    · linarith only [h14397, h16040, hlam]
                                  · have p15928_0 := h15928c.1
                                    have p15928_1 := h15928c.2.1
                                    have p15928_2 := h15928c.2.2.1
                                    have p15928_3 := h15928c.2.2.2
                                    linarith only [hlam, p15928_0]
                  · linarith only [h0, h15888, h15913, hlam]
                · linarith only [h0, h15887, h15912, hlam]
              · linarith only [h0, h15886, h15911, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h16047 | h16047
        · rcases m.htr 0 3 5 (by decide) (by decide) with h16048 | h16048
          · linarith only [h0, h14396, h15888, h16048, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h16050 | h16050
            · linarith only [h0, h14397, h15888, h16050, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16052 | h16052
              · rcases m.htr 1 2 4 (by decide) (by decide) with h16053 | h16053
                · rcases m.htr 1 2 5 (by decide) (by decide) with h16054 | h16054
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h16055 | h16055
                    · linarith only [h0, h14396, h15888, h16054, h16055, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h14396, h15888, h16047, h16052, h16054, h16055, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h16058 | h16058
                    · linarith only [h0, h14396, h16054, h16058, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h14396, h16047, h16052, h16054, h16058, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h15887, h16053, hlam]
              · linarith only [h0, h15886, h16052, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h16063 | h16063
          · linarith only [h0, h14397, h15888, h16047, h16063, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h16065 | h16065
            · linarith only [h0, h14397, h15888, h16065, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16067 | h16067
              · rcases m.htr 1 2 4 (by decide) (by decide) with h16068 | h16068
                · rcases m.htr 1 2 5 (by decide) (by decide) with h16069 | h16069
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h16070 | h16070
                    · linarith only [h0, h14396, h15888, h16047, h16069, h16070, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h16072 | h16072
                      · linarith only [h0, h14396, h15888, h16063, h16072, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h16074 | h16074
                        · linarith only [h0, h14397, h15888, h16065, h16069, h16074, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h16076 | h16076
                          · linarith only [h15886, h15888, h16047, h16069, h16076, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h16078 | h16078
                            · linarith only [h0, h14396, h15888, h16047, h16067, h16069, h16072, h16078, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h16080 | h16080
                              · linarith only [h0, h14397, h15888, h16068, h16069, h16074, h16080, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h16082 | h16082
                                · linarith only [h0, h14397, h15888, h16067, h16069, h16070, h16074, h16082, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c | h16084c
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h0, hlam, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h0, h14396, h15888, h16067, h16069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h0, h14396, h15888, h16047, h16067, h16069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h14398, hlam, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h15888, h16069, hc01, hc12, hlam, hphi, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h14396, h15888, h16067, h16069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h14396, h15888, h16047, h16067, h16069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h15888, hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h14396, hlam, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h15886, hlam, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h16047, hlam, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h16063, hlam, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h14397, hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h15887, hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h0, h14396, h14397, h15888, h16067, h16069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h16065, hlam, p16084_0]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h14396, h14398, h16067, h16072, h16082, hc23, hc45, hlam, hphi, ht34, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [h0, h14396, h15888, h16067, h16069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16084_1]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    rcases p16084_3 (m.d 0 1) (by simp) with h16107 | h16107
                                    · linarith only [h14398, h16107, hlam]
                                    · linarith only [h14396, h16107, hlam]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    rcases p16084_3 (m.d 0 1) (by simp) with h16110 | h16110
                                    · linarith only [h14398, h16110, hlam]
                                    · linarith only [h14397, h16110, hlam]
                                  · have p16084_0 := h16084c.1
                                    have p16084_1 := h16084c.2.1
                                    have p16084_2 := h16084c.2.2.1
                                    have p16084_3 := h16084c.2.2.2
                                    linarith only [hlam, p16084_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h16114 | h16114
                    · linarith only [h0, h14396, h16069, h16114, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h16116 | h16116
                      · linarith only [h0, h14397, h16069, h16114, h16116, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h16118 | h16118
                        · linarith only [h0, h14397, h16065, h16069, h16118, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h16120 | h16120
                          · linarith only [h14396, h16047, h16067, h16120, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h16122 | h16122
                            · linarith only [h0, h14397, h16067, h16069, h16114, h16116, h16122, hlam]
                            · linarith only [h0, h14397, h16067, h16069, h16114, h16122, hc23, hc35, hlam, hphi]
                · linarith only [h0, h14397, h15887, h15888, h16068, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h15886, h16067, hlam]
    · linarith only [h0, h14397, h15887, hlam]
  · linarith only [h0, h14396, h15886, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h14396 := hg14396
  rcases m.htr 0 1 5 (by decide) (by decide) with h14398 | h14398
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h14397 h14398

end R2N4
