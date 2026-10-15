import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S36
import Jsp000404.R1LeavesN7_2S37
import Jsp000404.R1LeavesN7_2S38

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 2 3 (by decide) (by decide) with h25935 | h25935
  · rcases m.htr 1 2 4 (by decide) (by decide) with h25936 | h25936
    · rcases m.htr 1 2 5 (by decide) (by decide) with h25937 | h25937
      · rcases m.htr 1 3 4 (by decide) (by decide) with h25938 | h25938
        · rcases m.htr 1 3 5 (by decide) (by decide) with h25939 | h25939
          · rcases m.htr 1 4 5 (by decide) (by decide) with h25940 | h25940
            · rcases m.htr 2 3 4 (by decide) (by decide) with h25941 | h25941
              · linarith only [h20408, h20411, h25941, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h25943 | h25943
                · linarith only [h20408, h24656, h25943, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25945 | h25945
                  · linarith only [h20409, h25076, h25945, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h25947 | h25947
                    · linarith only [h16915, h25076, h25935, h25938, h25947, hc01, hc12, hlam, hphi]
                    · linarith only [h14396, h20411, h25935, h25938, h25940, h25947, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h25950 | h25950
              · linarith only [h20408, h20411, h25950, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h25952 | h25952
                · linarith only [h20408, h24656, h25952, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25954 | h25954
                  · linarith only [h16915, h25940, h25954, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h25956 | h25956
                    · linarith only [h25938, h25940, h25956, hlam]
                    · rcases h0bigk with h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c | h25958c
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h0, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h14396, hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h16915, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h18815, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        rcases p25958_3 (m.d 0 1) (by simp) with h25964 | h25964
                        · linarith only [h0, h25964, hlam]
                        · rcases p25958_3 (m.d 0 2) (by simp) with h25966 | h25966
                          · rcases p25958_3 (m.d 0 3) (by simp) with h25967 | h25967
                            · linarith only [h20408, h25967, hlam]
                            · linarith only [h14396, h25967, hlam]
                          · linarith only [h0, h25966, hlam]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        rcases p25958_3 (m.d 0 1) (by simp) with h25972 | h25972
                        · linarith only [h0, h25972, hlam]
                        · rcases p25958_3 (m.d 0 2) (by simp) with h25974 | h25974
                          · rcases p25958_3 (m.d 0 3) (by simp) with h25975 | h25975
                            · linarith only [h20408, h25975, hlam]
                            · rcases p25958_3 (m.d 0 4) (by simp) with h25977 | h25977
                              · linarith only [h20409, h25977, hlam]
                              · linarith only [h20411, h25977, hlam]
                          · linarith only [h20408, h25974, hlam]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        rcases p25958_3 (m.d 0 1) (by simp) with h25981 | h25981
                        · linarith only [h0, h25981, hlam]
                        · rcases p25958_3 (m.d 0 2) (by simp) with h25983 | h25983
                          · rcases p25958_3 (m.d 0 3) (by simp) with h25984 | h25984
                            · linarith only [h20408, h25984, hlam]
                            · rcases p25958_3 (m.d 0 4) (by simp) with h25986 | h25986
                              · linarith only [h20409, h25986, hlam]
                              · rcases p25958_3 (m.d 0 5) (by simp) with h25988 | h25988
                                · linarith only [h20410, h25988, hlam]
                                · linarith only [h25076, h25988, hlam]
                          · linarith only [h20409, h25983, hlam]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        rcases p25958_3 (m.d 0 1) (by simp) with h25992 | h25992
                        · linarith only [h0, h25992, hlam]
                        · rcases p25958_3 (m.d 0 2) (by simp) with h25994 | h25994
                          · rcases p25958_3 (m.d 0 3) (by simp) with h25995 | h25995
                            · linarith only [h20408, h25995, hlam]
                            · rcases p25958_3 (m.d 0 4) (by simp) with h25997 | h25997
                              · linarith only [h20409, h25997, hlam]
                              · rcases p25958_3 (m.d 0 5) (by simp) with h25999 | h25999
                                · linarith only [h20410, h25999, hlam]
                                · rcases h2bigk with h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c | h26001c
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h0, hlam, p26001_1]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    rcases p26001_3 (m.d 0 2) (by simp) with h26004 | h26004
                                    · rcases p26001_3 (m.d 1 2) (by simp) with h26005 | h26005
                                      · rcases p26001_3 (m.d 2 3) (by simp) with h26006 | h26006
                                        · linarith only [h26006, hlam, p26001_0]
                                        · rcases p26001_3 (m.d 2 4) (by simp) with h26008 | h26008
                                          · linarith only [h20409, h26008, hlam]
                                          · linarith only [h25950, h26008, hlam]
                                      · linarith only [h25935, h26005, hlam]
                                    · linarith only [h26004, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    rcases p26001_3 (m.d 0 2) (by simp) with h26013 | h26013
                                    · rcases p26001_3 (m.d 1 2) (by simp) with h26014 | h26014
                                      · rcases p26001_3 (m.d 2 3) (by simp) with h26015 | h26015
                                        · linarith only [h20408, h26015, hlam]
                                        · rcases p26001_3 (m.d 2 4) (by simp) with h26017 | h26017
                                          · linarith only [h26017, hlam, p26001_0]
                                          · rcases p26001_3 (m.d 2 5) (by simp) with h26019 | h26019
                                            · linarith only [h20410, h26019, hlam]
                                            · linarith only [h25954, h26019, hlam]
                                      · linarith only [h25936, h26014, hlam]
                                    · linarith only [h26013, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    rcases p26001_3 (m.d 0 2) (by simp) with h26024 | h26024
                                    · rcases p26001_3 (m.d 1 2) (by simp) with h26025 | h26025
                                      · rcases p26001_3 (m.d 2 3) (by simp) with h26026 | h26026
                                        · linarith only [h20408, h26026, hlam]
                                        · rcases p26001_3 (m.d 2 4) (by simp) with h26028 | h26028
                                          · linarith only [h20409, h26028, hlam]
                                          · rcases p26001_3 (m.d 2 5) (by simp) with h26030 | h26030
                                            · linarith only [h26030, hlam, p26001_0]
                                            · rcases h3bigk with h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c | h26032c
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h14396, hlam, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h20411, h25938, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h20411, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h24656, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h14396, h25935, hc01, hc12, hlam, hphi, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                rcases p26032_3 (m.d 0 3) (by simp) with h26040 | h26040
                                                · linarith only [h14396, h26040, hlam]
                                                · linarith only [h20408, h26040, hlam]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h14396, h20411, h25935, hc01, hc12, hlam, hphi, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h14396, h24656, h25935, hc01, hc12, hlam, hphi, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h20408, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25935, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25950, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25952, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25938, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25938, h25940, hc23, hc45, hlam, hphi, ht34, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25956, hlam, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25939, hlam, p26032_0]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25935, h25939, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [h25935, h25939, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26032_1]
                                              · have p26032_0 := h26032c.1
                                                have p26032_1 := h26032c.2.1
                                                have p26032_2 := h26032c.2.2.1
                                                have p26032_3 := h26032c.2.2.2
                                                linarith only [hlam, p26032_0]
                                      · linarith only [h25937, h26025, hlam]
                                    · linarith only [h26024, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25076, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p25958_1, p26001_1]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    rcases p26001_3 (m.d 0 2) (by simp) with h26064 | h26064
                                    · linarith only [h0, h26064, hlam]
                                    · linarith only [h20408, h26064, hlam]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    rcases p26001_3 (m.d 0 2) (by simp) with h26067 | h26067
                                    · linarith only [h0, h26067, hlam]
                                    · linarith only [h20409, h26067, hlam]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    rcases p26001_3 (m.d 0 2) (by simp) with h26070 | h26070
                                    · linarith only [h0, h26070, hlam]
                                    · linarith only [h20410, h26070, hlam]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h20408, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25935, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25950, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25952, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h20409, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25936, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h16915, h20409, h25940, hc23, hc45, hlam, hphi, ht34, p26001_1]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25954, hlam, p26001_1]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h20410, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h25937, hlam, p26001_0]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h0, h20410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25958_1, p26001_1]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [h0, h20410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p25958_1, p26001_1]
                                  · have p26001_0 := h26001c.1
                                    have p26001_1 := h26001c.2.1
                                    have p26001_2 := h26001c.2.2.1
                                    have p26001_3 := h26001c.2.2.2
                                    linarith only [hlam, p26001_0]
                          · linarith only [h20410, h25994, hlam]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h20411, hc01, hc34, hlam, hphi, ht12, ht23, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h20408, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h20411, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h24656, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h16915, h25940, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h20409, hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h16915, h25940, hc03, hc45, hlam, hphi, ht34, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h25076, hlam, p25958_0]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h24656, h25935, h25939, hc01, hc12, hlam, hphi, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h20410, hlam, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h14396, h24656, h25935, h25939, hc01, hc12, hlam, hphi, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [h16915, h24656, h25935, h25939, hc01, hc12, hlam, hphi, p25958_1]
                      · have p25958_0 := h25958c.1
                        have p25958_1 := h25958c.2.1
                        have p25958_2 := h25958c.2.2.1
                        have p25958_3 := h25958c.2.2.2
                        linarith only [hlam, p25958_0]
          · linarith only [h14396, h20411, h25938, h25939, hc01, hc35, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h26105 | h26105
          · linarith only [h14396, h24656, h25938, h26105, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h26107 | h26107
            · rcases m.htr 2 3 4 (by decide) (by decide) with h26108 | h26108
              · linarith only [h14396, h25938, h26108, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h26110 | h26110
                · linarith only [h14396, h20408, h20411, h25076, h26105, h26107, h26110, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h26112 | h26112
                  · linarith only [h0, h14396, h20409, h20411, h25076, h26112, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h26114 | h26114
                    · rcases h0bigk with h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c | h26115c
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h0, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h14396, hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h16915, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h18815, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        rcases p26115_3 (m.d 0 1) (by simp) with h26121 | h26121
                        · linarith only [h0, h26121, hlam]
                        · rcases p26115_3 (m.d 0 2) (by simp) with h26123 | h26123
                          · rcases p26115_3 (m.d 0 3) (by simp) with h26124 | h26124
                            · linarith only [h20408, h26124, hlam]
                            · linarith only [h14396, h26124, hlam]
                          · linarith only [h0, h26123, hlam]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        rcases p26115_3 (m.d 0 1) (by simp) with h26129 | h26129
                        · linarith only [h0, h26129, hlam]
                        · rcases p26115_3 (m.d 0 2) (by simp) with h26131 | h26131
                          · rcases p26115_3 (m.d 0 3) (by simp) with h26132 | h26132
                            · linarith only [h20408, h26132, hlam]
                            · rcases p26115_3 (m.d 0 4) (by simp) with h26134 | h26134
                              · linarith only [h20409, h26134, hlam]
                              · linarith only [h20411, h26134, hlam]
                          · linarith only [h20408, h26131, hlam]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        rcases p26115_3 (m.d 0 1) (by simp) with h26138 | h26138
                        · linarith only [h0, h26138, hlam]
                        · rcases p26115_3 (m.d 0 2) (by simp) with h26140 | h26140
                          · rcases p26115_3 (m.d 0 3) (by simp) with h26141 | h26141
                            · linarith only [h20408, h26141, hlam]
                            · rcases p26115_3 (m.d 0 4) (by simp) with h26143 | h26143
                              · linarith only [h20409, h26143, hlam]
                              · rcases p26115_3 (m.d 0 5) (by simp) with h26145 | h26145
                                · linarith only [h20410, h26145, hlam]
                                · linarith only [h25076, h26145, hlam]
                          · linarith only [h20409, h26140, hlam]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        rcases p26115_3 (m.d 0 1) (by simp) with h26149 | h26149
                        · linarith only [h0, h26149, hlam]
                        · rcases p26115_3 (m.d 0 2) (by simp) with h26151 | h26151
                          · rcases p26115_3 (m.d 0 3) (by simp) with h26152 | h26152
                            · linarith only [h20408, h26152, hlam]
                            · rcases p26115_3 (m.d 0 4) (by simp) with h26154 | h26154
                              · linarith only [h20409, h26154, hlam]
                              · rcases p26115_3 (m.d 0 5) (by simp) with h26156 | h26156
                                · linarith only [h20410, h26156, hlam]
                                · rcases h2bigk with h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c | h26158c
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h0, hlam, p26158_1]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    rcases p26158_3 (m.d 0 2) (by simp) with h26161 | h26161
                                    · rcases p26158_3 (m.d 1 2) (by simp) with h26162 | h26162
                                      · rcases p26158_3 (m.d 2 3) (by simp) with h26163 | h26163
                                        · linarith only [h26163, hlam, p26158_0]
                                        · rcases p26158_3 (m.d 2 4) (by simp) with h26165 | h26165
                                          · linarith only [h20409, h26165, hlam]
                                          · linarith only [h26108, h26165, hlam]
                                      · linarith only [h25935, h26162, hlam]
                                    · linarith only [h26161, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    rcases p26158_3 (m.d 0 2) (by simp) with h26170 | h26170
                                    · rcases p26158_3 (m.d 1 2) (by simp) with h26171 | h26171
                                      · rcases p26158_3 (m.d 2 3) (by simp) with h26172 | h26172
                                        · linarith only [h20408, h26172, hlam]
                                        · rcases p26158_3 (m.d 2 4) (by simp) with h26174 | h26174
                                          · linarith only [h26174, hlam, p26158_0]
                                          · rcases p26158_3 (m.d 2 5) (by simp) with h26176 | h26176
                                            · linarith only [h20410, h26176, hlam]
                                            · linarith only [h26112, h26176, hlam]
                                      · linarith only [h25936, h26171, hlam]
                                    · linarith only [h26170, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    rcases p26158_3 (m.d 0 2) (by simp) with h26181 | h26181
                                    · rcases p26158_3 (m.d 1 2) (by simp) with h26182 | h26182
                                      · rcases p26158_3 (m.d 2 3) (by simp) with h26183 | h26183
                                        · linarith only [h20408, h26183, hlam]
                                        · rcases p26158_3 (m.d 2 4) (by simp) with h26185 | h26185
                                          · linarith only [h20409, h26185, hlam]
                                          · rcases p26158_3 (m.d 2 5) (by simp) with h26187 | h26187
                                            · linarith only [h26187, hlam, p26158_0]
                                            · rcases h3bigk with h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c | h26189c
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h14396, hlam, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h20411, h25076, h26107, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h20411, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h24656, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h14396, hc01, hc13, hlam, hphi, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h25938, hc23, hc34, hlam, hphi, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h25938, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h26105, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h20408, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h25935, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h26108, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h26110, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hc13, hc34, hlam, hphi, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h14396, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p26189_1]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [h26114, hlam, p26189_0]
                                              · have p26189_0 := h26189c.1
                                                have p26189_1 := h26189c.2.1
                                                have p26189_2 := h26189c.2.2.1
                                                have p26189_3 := h26189c.2.2.2
                                                linarith only [hlam, p26189_0]
                                      · linarith only [h25937, h26182, hlam]
                                    · linarith only [h26181, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p26115_1, p26158_1]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    rcases p26158_3 (m.d 0 2) (by simp) with h26219 | h26219
                                    · linarith only [h0, h26219, hlam]
                                    · linarith only [h20408, h26219, hlam]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    rcases p26158_3 (m.d 0 2) (by simp) with h26222 | h26222
                                    · linarith only [h0, h26222, hlam]
                                    · linarith only [h20409, h26222, hlam]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    rcases p26158_3 (m.d 0 2) (by simp) with h26225 | h26225
                                    · linarith only [h0, h26225, hlam]
                                    · linarith only [h20410, h26225, hlam]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h20408, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h25935, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h26108, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h26110, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h20409, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h25936, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h20409, h25076, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26115_1, p26158_1]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h26112, hlam, p26158_1]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h20410, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h25937, hlam, p26158_0]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h20410, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26115_1, p26158_1]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [h0, h20410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p26115_1, p26158_1]
                                  · have p26158_0 := h26158c.1
                                    have p26158_1 := h26158c.2.1
                                    have p26158_2 := h26158c.2.2.1
                                    have p26158_3 := h26158c.2.2.2
                                    linarith only [hlam, p26158_0]
                          · linarith only [h20410, h26151, hlam]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h20411, h25076, h25938, h26107, hc01, hc34, hlam, hphi, ht12, ht23, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h20408, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h20411, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h24656, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h25076, h25938, h26107, hc01, hc34, hlam, hphi, ht12, ht23, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h20409, hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h25076, h25938, h26107, hc03, hc34, hlam, hphi, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h25076, hlam, p26115_0]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h25076, h25938, h26107, hc01, hc34, hlam, hphi, ht12, ht23, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h20410, hlam, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h14396, h25076, h25938, h26107, hc01, hc34, hlam, hphi, ht12, ht23, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [h16915, h25076, h25938, h26107, hc01, hc34, hlam, hphi, ht12, ht23, p26115_1]
                      · have p26115_0 := h26115c.1
                        have p26115_1 := h26115c.2.1
                        have p26115_2 := h26115c.2.2.1
                        have p26115_3 := h26115c.2.2.2
                        linarith only [hlam, p26115_0]
                    · linarith only [h25938, h26107, h26114, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h26260 | h26260
              · linarith only [h20408, h20411, h26260, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h26262 | h26262
                · linarith only [h0, h18815, h20408, h26105, h26262, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h26264 | h26264
                  · linarith only [h16915, h26107, h26264, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h26266 | h26266
                    · linarith only [h14396, h25938, h26107, h26266, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h14396, h25938, h26266, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h20410, h25937, hlam]
    · linarith only [h0, h20409, h25936, hlam]
  · linarith only [h0, h20408, h25935, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 0 4 5 (by decide) (by decide) with h25076 | h25076
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 0 3 5 (by decide) (by decide) with h24656 | h24656
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 0 3 4 (by decide) (by decide) with h20411 | h20411
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411

set_option maxHeartbeats 11980000 in
set_option maxHeartbeats 11980000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s20 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  rcases m.htr 0 2 5 (by decide) (by decide) with h20410 | h20410
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21 m hb0 hb2 hb3 h0 h14396 h16915 h18815 h20408 h20409 h20410
  · rcases m.htr 0 3 4 (by decide) (by decide) with h26272 | h26272
    · rcases m.htr 0 3 5 (by decide) (by decide) with h26273 | h26273
      · linarith only [h20408, h20410, h26273, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h26275 | h26275
        · linarith only [h20409, h20410, h26275, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h26277 | h26277
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26278 | h26278
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26279 | h26279
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26280 | h26280
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26281 | h26281
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26282 | h26282
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26283 | h26283
                      · linarith only [h20408, h20410, h26279, h26283, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h20408, h20410, h26272, h26279, h26283, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26286 | h26286
                      · linarith only [h20408, h20410, h26279, h26286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h20408, h20410, h26272, h26279, h26286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26289 | h26289
                    · linarith only [h16915, h26275, h26280, h26281, h26289, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26291 | h26291
                      · linarith only [h20408, h20410, h26279, h26291, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h20408, h20410, h26272, h26279, h26291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h14396, h20408, h20410, h26272, h26279, h26280, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26295 | h26295
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26296 | h26296
                  · linarith only [h26272, h26273, h26277, h26279, h26296, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26298 | h26298
                    · linarith only [h16915, h26275, h26278, h26279, h26298, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26300 | h26300
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26301 | h26301
                        · linarith only [h0, h20408, h26279, h26296, h26301, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26303 | h26303
                          · linarith only [h20409, h26275, h26303, hlam]
                          · linarith only [h0, h20408, h26279, h26300, h26303, hc34, hc45, hlam, hphi]
                      · linarith only [h26272, h26273, h26300, hc23, hc35, hlam, hphi]
                · linarith only [h14396, h26272, h26295, hlam]
            · linarith only [h0, h20409, h26278, hlam]
          · linarith only [h0, h20408, h26277, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h26310 | h26310
      · linarith only [h20409, h20410, h26272, h26310, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h26312 | h26312
        · linarith only [h20409, h20410, h26312, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h26314 | h26314
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26315 | h26315
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26316 | h26316
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26317 | h26317
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26318 | h26318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26319 | h26319
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26320 | h26320
                      · linarith only [h0, h14396, h20408, h26272, h26320, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26322 | h26322
                        · linarith only [h20409, h20410, h26310, h26316, h26320, h26322, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26324 | h26324
                          · linarith only [h20409, h20410, h26314, h26318, h26322, h26324, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26326 | h26326
                            · linarith only [h20409, h20410, h26320, h26324, h26326, hc23, hc34, hlam, hphi]
                            · linarith only [h14396, h26272, h26314, h26317, h26319, h26326, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26329 | h26329
                      · linarith only [h14396, h20408, h20410, h26272, h26329, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26331 | h26331
                        · linarith only [h20409, h20410, h26310, h26316, h26329, h26331, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26333 | h26333
                          · linarith only [h20409, h20410, h26314, h26318, h26319, h26331, h26333, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26335 | h26335
                            · linarith only [h26317, h26319, h26335, hlam]
                            · rcases h0bigk with h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c | h26337c
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h0, hlam, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h14396, hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h16915, hlam, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h18815, hlam, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20410, h26314, h26318, h26331, hc01, hc12, hlam, hphi, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h14396, h20410, h26314, h26318, h26331, hc01, hc12, hlam, hphi, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20410, h26314, h26318, h26331, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20410, hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h26272, h26317, hc01, hc14, hlam, hphi, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20408, hlam, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h26272, hlam, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h26310, hlam, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h16915, h20409, h20410, h26314, h26318, h26319, h26329, h26331, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20409, hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20409, h20410, h26314, h26318, h26331, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h26312, hlam, p26337_0]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20410, h26314, h26318, h26331, hc01, hc12, hlam, hphi, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h20409, h20410, h26314, h26318, h26329, h26331, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h14396, h20410, h26314, h26318, h26331, hc01, hc12, hlam, hphi, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [h16915, h20410, h26314, h26318, h26331, hc01, hc12, hlam, hphi, p26337_1]
                              · have p26337_0 := h26337c.1
                                have p26337_1 := h26337c.2.1
                                have p26337_2 := h26337c.2.2.1
                                have p26337_3 := h26337c.2.2.2
                                linarith only [hlam, p26337_0]
                  · linarith only [h14396, h26272, h26317, h26318, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26364 | h26364
                  · linarith only [h14396, h26310, h26317, h26364, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26366 | h26366
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26367 | h26367
                      · linarith only [h14396, h20408, h26317, h26367, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26369 | h26369
                        · linarith only [h20409, h20410, h26316, h26367, h26369, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26371 | h26371
                          · linarith only [h14396, h20409, h20410, h26272, h26312, h26316, h26371, hc01, hc12, hlam, hphi]
                          · linarith only [h20409, h20410, h26317, h26366, h26367, h26371, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26374 | h26374
                      · linarith only [h20408, h20410, h26316, h26374, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26376 | h26376
                        · linarith only [h20409, h20410, h26316, h26374, h26376, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26378 | h26378
                          · linarith only [h20409, h20410, h26316, h26366, h26378, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26380 | h26380
                            · linarith only [h14396, h26317, h26366, h26380, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h14396, h26317, h26380, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26383 | h26383
                · linarith only [h14396, h26272, h26314, h26316, h26383, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26385 | h26385
                  · linarith only [h14396, h26310, h26315, h26316, h26383, h26385, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26387 | h26387
                    · linarith only [h16915, h26312, h26315, h26316, h26387, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26389 | h26389
                      · linarith only [h14396, h26383, h26389, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26391 | h26391
                        · linarith only [h0, h18815, h20409, h26316, h26385, h26389, h26391, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26393 | h26393
                          · linarith only [h14396, h18815, h20409, h20410, h26272, h26312, h26393, hc01, hc15, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26395 | h26395
                            · linarith only [h0, h26316, h26393, h26395, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h14396, h26383, h26395, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h20409, h26315, hlam]
          · linarith only [h0, h20408, h26314, hlam]

end R2N4
