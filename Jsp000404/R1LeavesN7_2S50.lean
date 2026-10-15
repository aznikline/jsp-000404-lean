import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S47
import Jsp000404.R1LeavesN7_2S49

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h17960 | h17960
  · rcases m.htr 0 2 4 (by decide) (by decide) with h17961 | h17961
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17962 | h17962
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17963 | h17963
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17964 | h17964
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17965 | h17965
            · linarith only [h16915, h16916, h17965, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17967 | h17967
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17968 | h17968
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17969 | h17969
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17970 | h17970
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17971 | h17971
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17972 | h17972
                        · linarith only [h16915, h16916, h17965, h17967, h17971, h17972, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17974 | h17974
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17975 | h17975
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17976 | h17976
                              · linarith only [h16915, h16916, h17968, h17972, h17976, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17978 | h17978
                                · linarith only [h16916, h17960, h17972, h17974, h17978, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h0bigk with h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c | h17980c
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h0, hlam, p17980_1]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h14396, hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h16916, h17972, hc04, hc45, hlam, hphi, p17980_1]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h16916, hlam, p17980_1]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h17986 | h17986
                                    · linarith only [h0, h17986, hlam]
                                    · rcases p17980_3 (m.d 0 2) (by simp) with h17988 | h17988
                                      · rcases p17980_3 (m.d 0 3) (by simp) with h17989 | h17989
                                        · linarith only [h17960, h17989, hlam]
                                        · linarith only [h14396, h17989, hlam]
                                      · linarith only [h0, h17988, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h17994 | h17994
                                    · linarith only [h0, h17994, hlam]
                                    · rcases p17980_3 (m.d 0 2) (by simp) with h17996 | h17996
                                      · rcases p17980_3 (m.d 0 3) (by simp) with h17997 | h17997
                                        · linarith only [h17960, h17997, hlam]
                                        · rcases p17980_3 (m.d 0 4) (by simp) with h17999 | h17999
                                          · linarith only [h17961, h17999, hlam]
                                          · rcases p17980_3 (m.d 0 5) (by simp) with h18001 | h18001
                                            · linarith only [h17962, h18001, hlam]
                                            · rcases h2bigk with h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c | h18003c
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h0, hlam, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                rcases p18003_3 (m.d 0 2) (by simp) with h18006 | h18006
                                                · rcases p18003_3 (m.d 1 2) (by simp) with h18007 | h18007
                                                  · rcases p18003_3 (m.d 2 3) (by simp) with h18008 | h18008
                                                    · linarith only [h18008, hlam, p18003_0]
                                                    · rcases p18003_3 (m.d 2 4) (by simp) with h18010 | h18010
                                                      · linarith only [h17961, h18010, hlam]
                                                      · rcases p18003_3 (m.d 2 5) (by simp) with h18012 | h18012
                                                        · linarith only [h17962, h18012, hlam]
                                                        · rcases h3bigk with h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c | h18014c
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h14396, hlam, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h0, h17975, h17978, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h0, h17978, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h16916, h17964, hc01, hc13, hlam, hphi, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17967, h17975, h17978, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            rcases p18014_3 (m.d 0 3) (by simp) with h18023 | h18023
                                                            · linarith only [h14396, h18023, hlam]
                                                            · linarith only [h17963, h18023, hlam]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            rcases p18014_3 (m.d 0 3) (by simp) with h18026 | h18026
                                                            · linarith only [h14396, h18026, hlam]
                                                            · linarith only [h17964, h18026, hlam]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17960, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17967, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18003_1, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h0, h17960, h17978, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17963, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17970, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17974, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17978, hlam, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17964, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17971, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h17975, hlam, p18014_0]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [h0, h17964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18014_1]
                                                          · have p18014_0 := h18014c.1
                                                            have p18014_1 := h18014c.2.1
                                                            have p18014_2 := h18014c.2.2.1
                                                            have p18014_3 := h18014c.2.2.2
                                                            linarith only [hlam, p18014_0]
                                                  · linarith only [h17967, h18007, hlam]
                                                · linarith only [h18006, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h14396, h16915, h17968, hlam, p17980_1, p18003_2]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                rcases p18003_3 (m.d 0 2) (by simp) with h18047 | h18047
                                                · rcases p18003_3 (m.d 1 2) (by simp) with h18048 | h18048
                                                  · rcases p18003_3 (m.d 2 3) (by simp) with h18049 | h18049
                                                    · linarith only [h17960, h18049, hlam]
                                                    · linarith only [h17975, h18049, hlam]
                                                  · linarith only [h17969, h18048, hlam]
                                                · linarith only [h18047, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h16916, h17964, hc01, hc12, hlam, hphi, p17980_1, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                rcases p18003_3 (m.d 0 2) (by simp) with h18056 | h18056
                                                · linarith only [h0, h18056, hlam]
                                                · linarith only [h17960, h18056, hlam]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h0, h16915, h16916, h17964, h17968, hlam, p17980_1, p18003_2]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                rcases p18003_3 (m.d 0 2) (by simp) with h18060 | h18060
                                                · linarith only [h0, h18060, hlam]
                                                · linarith only [h17962, h18060, hlam]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17960, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17967, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17960, h17974, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p17980_1, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h0, h17960, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p17980_1, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17961, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17968, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17974, hlam, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17976, hlam, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17962, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17969, hlam, p18003_0]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h17975, hlam, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [h0, h17962, h17964, h17974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18003_1]
                                              · have p18003_0 := h18003c.1
                                                have p18003_1 := h18003c.2.1
                                                have p18003_2 := h18003c.2.2.1
                                                have p18003_3 := h18003c.2.2.2
                                                linarith only [hlam, p18003_0]
                                      · linarith only [h17960, h17996, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h18079 | h18079
                                    · linarith only [h0, h18079, hlam]
                                    · linarith only [h16915, h18079, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h18082 | h18082
                                    · linarith only [h0, h18082, hlam]
                                    · rcases p17980_3 (m.d 0 2) (by simp) with h18084 | h18084
                                      · rcases p17980_3 (m.d 0 3) (by simp) with h18085 | h18085
                                        · linarith only [h17960, h18085, hlam]
                                        · linarith only [h17964, h18085, hlam]
                                      · linarith only [h17962, h18084, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h18089 | h18089
                                    · linarith only [h14396, h18089, hlam]
                                    · rcases p17980_3 (m.d 0 2) (by simp) with h18091 | h18091
                                      · rcases p17980_3 (m.d 0 3) (by simp) with h18092 | h18092
                                        · rcases p17980_3 (m.d 0 4) (by simp) with h18093 | h18093
                                          · linarith only [h17963, h18093, hlam]
                                          · rcases p17980_3 (m.d 0 5) (by simp) with h18095 | h18095
                                            · linarith only [h17964, h18095, hlam]
                                            · linarith only [h16916, h18095, hlam]
                                        · linarith only [h14396, h18092, hlam]
                                      · linarith only [h0, h18091, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h17960, hlam, p17980_1]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h18102 | h18102
                                    · linarith only [h14396, h18102, hlam]
                                    · linarith only [h16915, h18102, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h18105 | h18105
                                    · linarith only [h14396, h18105, hlam]
                                    · rcases p17980_3 (m.d 0 2) (by simp) with h18107 | h18107
                                      · rcases p17980_3 (m.d 0 3) (by simp) with h18108 | h18108
                                        · rcases p17980_3 (m.d 0 4) (by simp) with h18109 | h18109
                                          · linarith only [h17963, h18109, hlam]
                                          · rcases p17980_3 (m.d 0 5) (by simp) with h18111 | h18111
                                            · linarith only [h17964, h18111, hlam]
                                            · rcases h2bigk with h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c | h18113c
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h0, hlam, p18113_1]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                rcases p18113_3 (m.d 0 2) (by simp) with h18116 | h18116
                                                · rcases p18113_3 (m.d 1 2) (by simp) with h18117 | h18117
                                                  · rcases p18113_3 (m.d 2 3) (by simp) with h18118 | h18118
                                                    · linarith only [h18118, hlam, p18113_0]
                                                    · rcases p18113_3 (m.d 2 4) (by simp) with h18120 | h18120
                                                      · linarith only [h17961, h18120, hlam]
                                                      · rcases p18113_3 (m.d 2 5) (by simp) with h18122 | h18122
                                                        · linarith only [h17962, h18122, hlam]
                                                        · rcases h3bigk with h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c | h18124c
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h14396, hlam, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h14396, h17967, h17975, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            rcases p18124_3 (m.d 0 3) (by simp) with h18128 | h18128
                                                            · rcases p18124_3 (m.d 1 3) (by simp) with h18129 | h18129
                                                              · rcases p18124_3 (m.d 2 3) (by simp) with h18130 | h18130
                                                                · linarith only [h17960, h18130, hlam]
                                                                · linarith only [h17974, h18130, hlam]
                                                              · linarith only [h17970, h18129, hlam]
                                                            · linarith only [h18128, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            rcases p18124_3 (m.d 0 3) (by simp) with h18135 | h18135
                                                            · rcases p18124_3 (m.d 1 3) (by simp) with h18136 | h18136
                                                              · rcases p18124_3 (m.d 2 3) (by simp) with h18137 | h18137
                                                                · linarith only [h17960, h18137, hlam]
                                                                · linarith only [h17975, h18137, hlam]
                                                              · linarith only [h17971, h18136, hlam]
                                                            · linarith only [h18135, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17967, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p17980_1, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17967, h17974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            rcases p18124_3 (m.d 0 3) (by simp) with h18145 | h18145
                                                            · linarith only [h14396, h18145, hlam]
                                                            · linarith only [h17963, h18145, hlam]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            rcases p18124_3 (m.d 0 3) (by simp) with h18148 | h18148
                                                            · linarith only [h14396, h18148, hlam]
                                                            · linarith only [h17964, h18148, hlam]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17960, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17967, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18113_1, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h0, h17978, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18113_1, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17963, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17970, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17974, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17978, hlam, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17964, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17971, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h17975, hlam, p18124_0]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [h0, h17962, h17975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18124_1]
                                                          · have p18124_0 := h18124c.1
                                                            have p18124_1 := h18124c.2.1
                                                            have p18124_2 := h18124c.2.2.1
                                                            have p18124_3 := h18124c.2.2.2
                                                            linarith only [hlam, p18124_0]
                                                  · linarith only [h17967, h18117, hlam]
                                                · linarith only [h18116, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h16915, h16916, h17960, h17968, hlam, p17980_1, p18113_2]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                rcases p18113_3 (m.d 0 2) (by simp) with h18169 | h18169
                                                · rcases p18113_3 (m.d 1 2) (by simp) with h18170 | h18170
                                                  · rcases p18113_3 (m.d 2 3) (by simp) with h18171 | h18171
                                                    · linarith only [h17960, h18171, hlam]
                                                    · linarith only [h17975, h18171, hlam]
                                                  · linarith only [h17969, h18170, hlam]
                                                · linarith only [h18169, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h16915, h16916, h17960, h17968, h17974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18113_1]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                rcases p18113_3 (m.d 0 2) (by simp) with h18178 | h18178
                                                · linarith only [h0, h18178, hlam]
                                                · linarith only [h17960, h18178, hlam]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h0, h16915, h16916, h17960, h17968, hlam, p17980_1, p18113_2]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                rcases p18113_3 (m.d 0 2) (by simp) with h18182 | h18182
                                                · linarith only [h0, h18182, hlam]
                                                · linarith only [h17962, h18182, hlam]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17960, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17967, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                rcases p18113_3 (m.d 0 2) (by simp) with h18188 | h18188
                                                · rcases p18113_3 (m.d 1 2) (by simp) with h18189 | h18189
                                                  · rcases p18113_3 (m.d 2 3) (by simp) with h18190 | h18190
                                                    · rcases p18113_3 (m.d 2 4) (by simp) with h18191 | h18191
                                                      · linarith only [h17974, h18191, hlam]
                                                      · rcases p18113_3 (m.d 2 5) (by simp) with h18193 | h18193
                                                        · linarith only [h17975, h18193, hlam]
                                                        · linarith only [h17976, h18193, hlam]
                                                    · linarith only [h17974, h18190, hlam]
                                                  · linarith only [h17968, h18189, hlam]
                                                · linarith only [h17961, h18188, hlam]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                rcases p18113_3 (m.d 0 2) (by simp) with h18199 | h18199
                                                · rcases p18113_3 (m.d 1 2) (by simp) with h18200 | h18200
                                                  · rcases p18113_3 (m.d 2 3) (by simp) with h18201 | h18201
                                                    · rcases p18113_3 (m.d 2 4) (by simp) with h18202 | h18202
                                                      · linarith only [h17974, h18202, hlam]
                                                      · rcases p18113_3 (m.d 2 5) (by simp) with h18204 | h18204
                                                        · linarith only [h17975, h18204, hlam]
                                                        · rcases h3bigk with h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c | h18206c
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h14396, hlam, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17960, h17974, h17976, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18113_1, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            rcases p18206_3 (m.d 0 3) (by simp) with h18210 | h18210
                                                            · rcases p18206_3 (m.d 1 3) (by simp) with h18211 | h18211
                                                              · rcases p18206_3 (m.d 2 3) (by simp) with h18212 | h18212
                                                                · linarith only [h17960, h18212, hlam]
                                                                · linarith only [h17974, h18212, hlam]
                                                              · linarith only [h17970, h18211, hlam]
                                                            · linarith only [h18210, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            rcases p18206_3 (m.d 0 3) (by simp) with h18217 | h18217
                                                            · rcases p18206_3 (m.d 1 3) (by simp) with h18218 | h18218
                                                              · rcases p18206_3 (m.d 2 3) (by simp) with h18219 | h18219
                                                                · linarith only [h17960, h18219, hlam]
                                                                · linarith only [h17975, h18219, hlam]
                                                              · linarith only [h17971, h18218, hlam]
                                                            · linarith only [h18217, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h14396, h16915, h17967, h17968, h17974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17967, h17974, h17976, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18113_1, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            rcases p18206_3 (m.d 0 3) (by simp) with h18227 | h18227
                                                            · linarith only [h14396, h18227, hlam]
                                                            · linarith only [h17963, h18227, hlam]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            rcases p18206_3 (m.d 0 3) (by simp) with h18230 | h18230
                                                            · linarith only [h14396, h18230, hlam]
                                                            · linarith only [h17964, h18230, hlam]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17960, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17967, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h0, h17960, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h0, h17960, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17963, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17970, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17974, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17978, hlam, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17964, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17971, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17975, hlam, p18206_0]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [h17964, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18206_1]
                                                          · have p18206_0 := h18206c.1
                                                            have p18206_1 := h18206c.2.1
                                                            have p18206_2 := h18206c.2.2.1
                                                            have p18206_3 := h18206c.2.2.2
                                                            linarith only [hlam, p18206_0]
                                                    · linarith only [h17975, h18201, hlam]
                                                  · linarith only [h17969, h18200, hlam]
                                                · linarith only [h17962, h18199, hlam]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17961, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17968, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17974, hlam, p18113_1]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17976, hlam, p18113_1]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17962, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17969, hlam, p18113_0]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h17975, hlam, p18113_1]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [h14396, h17962, h17967, h17974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17980_1, p18113_1]
                                              · have p18113_0 := h18113c.1
                                                have p18113_1 := h18113c.2.1
                                                have p18113_2 := h18113c.2.2.1
                                                have p18113_3 := h18113c.2.2.2
                                                linarith only [hlam, p18113_0]
                                        · linarith only [h17964, h18108, hlam]
                                      · linarith only [h17962, h18107, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h16915, hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h17961, hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h17963, hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h17965, hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h16915, h16916, h17968, h17972, h17974, hc34, hc45, hlam, hphi, p17980_1]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h17962, hlam, p17980_1]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [h17964, hlam, p17980_0]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    rcases p17980_3 (m.d 0 1) (by simp) with h18271 | h18271
                                    · linarith only [h16916, h18271, hlam]
                                    · linarith only [h16915, h18271, hlam]
                                  · have p17980_0 := h17980c.1
                                    have p17980_1 := h17980c.2.1
                                    have p17980_2 := h17980c.2.2.1
                                    have p17980_3 := h17980c.2.2.2
                                    linarith only [hlam, p17980_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18275 | h18275
                              · linarith only [h16915, h16916, h17968, h17972, h18275, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18277 | h18277
                                · linarith only [h14396, h16916, h17964, h17967, h17972, h17974, h17975, h18277, hc01, hc12, hlam, hphi]
                                · rcases h0bigk with h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c | h18279c
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h0, hlam, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h14396, hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h16915, h16916, h17968, h17972, h17974, hc34, hc45, hlam, hphi, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h16916, hlam, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    rcases p18279_3 (m.d 0 1) (by simp) with h18285 | h18285
                                    · linarith only [h0, h18285, hlam]
                                    · rcases p18279_3 (m.d 0 2) (by simp) with h18287 | h18287
                                      · rcases p18279_3 (m.d 0 3) (by simp) with h18288 | h18288
                                        · linarith only [h17960, h18288, hlam]
                                        · linarith only [h14396, h18288, hlam]
                                      · linarith only [h0, h18287, hlam]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h0, h17964, h17975, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    rcases p18279_3 (m.d 0 1) (by simp) with h18294 | h18294
                                    · linarith only [h0, h18294, hlam]
                                    · linarith only [h16915, h18294, hlam]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h0, h17964, h17974, h17975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    rcases p18279_3 (m.d 0 1) (by simp) with h18298 | h18298
                                    · linarith only [h14396, h18298, hlam]
                                    · rcases p18279_3 (m.d 0 2) (by simp) with h18300 | h18300
                                      · rcases p18279_3 (m.d 0 3) (by simp) with h18301 | h18301
                                        · rcases p18279_3 (m.d 0 4) (by simp) with h18302 | h18302
                                          · linarith only [h17963, h18302, hlam]
                                          · rcases p18279_3 (m.d 0 5) (by simp) with h18304 | h18304
                                            · linarith only [h17964, h18304, hlam]
                                            · linarith only [h16916, h18304, hlam]
                                        · linarith only [h14396, h18301, hlam]
                                      · linarith only [h0, h18300, hlam]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17960, hlam, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    rcases p18279_3 (m.d 0 1) (by simp) with h18311 | h18311
                                    · linarith only [h14396, h18311, hlam]
                                    · linarith only [h16915, h18311, hlam]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17964, h17974, h17975, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h16915, hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17961, hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17963, hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17965, hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h16915, h16916, h17968, h17972, h17974, hc34, hc45, hlam, hphi, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17962, hlam, p18279_1]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [h17964, hlam, p18279_0]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    rcases p18279_3 (m.d 0 1) (by simp) with h18323 | h18323
                                    · linarith only [h16916, h18323, hlam]
                                    · linarith only [h16915, h18323, hlam]
                                  · have p18279_0 := h18279c.1
                                    have p18279_1 := h18279c.2.1
                                    have p18279_2 := h18279c.2.2.1
                                    have p18279_3 := h18279c.2.2.2
                                    linarith only [hlam, p18279_0]
                          · linarith only [h16915, h16916, h17970, h17972, h17974, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h14396, h17964, h17971, hlam]
                    · linarith only [h14396, h17963, h17970, hlam]
                  · linarith only [h0, h17962, h17969, hlam]
                · linarith only [h0, h17961, h17968, hlam]
              · linarith only [h0, h17960, h17967, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18333 | h18333
            · linarith only [h14396, h16915, h17964, h18333, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18335 | h18335
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18336 | h18336
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18337 | h18337
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18338 | h18338
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18339 | h18339
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18340 | h18340
                        · linarith only [h14396, h16915, h17964, h18333, h18335, h18339, h18340, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18342 | h18342
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18343 | h18343
                            · linarith only [h17960, h17964, h18343, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18345 | h18345
                              · linarith only [h14396, h16915, h17964, h18336, h18339, h18340, h18345, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18347 | h18347
                                · linarith only [h17963, h17964, h18339, h18340, h18347, hlam]
                                · rcases h0bigk with h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c | h18349c
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h0, hlam, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h14396, hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h14396, h17964, h18335, h18339, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h16916, hlam, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    rcases p18349_3 (m.d 0 1) (by simp) with h18355 | h18355
                                    · linarith only [h0, h18355, hlam]
                                    · rcases p18349_3 (m.d 0 2) (by simp) with h18357 | h18357
                                      · rcases p18349_3 (m.d 0 3) (by simp) with h18358 | h18358
                                        · linarith only [h17960, h18358, hlam]
                                        · linarith only [h14396, h18358, hlam]
                                      · linarith only [h0, h18357, hlam]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    rcases p18349_3 (m.d 0 1) (by simp) with h18363 | h18363
                                    · linarith only [h0, h18363, hlam]
                                    · rcases p18349_3 (m.d 0 2) (by simp) with h18365 | h18365
                                      · rcases p18349_3 (m.d 0 3) (by simp) with h18366 | h18366
                                        · linarith only [h17960, h18366, hlam]
                                        · rcases p18349_3 (m.d 0 4) (by simp) with h18368 | h18368
                                          · linarith only [h17961, h18368, hlam]
                                          · rcases p18349_3 (m.d 0 5) (by simp) with h18370 | h18370
                                            · linarith only [h17962, h18370, hlam]
                                            · linarith only [h17964, h18370, hlam]
                                      · linarith only [h17960, h18365, hlam]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    rcases p18349_3 (m.d 0 1) (by simp) with h18374 | h18374
                                    · linarith only [h0, h18374, hlam]
                                    · linarith only [h16915, h18374, hlam]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    rcases p18349_3 (m.d 0 1) (by simp) with h18377 | h18377
                                    · linarith only [h0, h18377, hlam]
                                    · rcases p18349_3 (m.d 0 2) (by simp) with h18379 | h18379
                                      · rcases p18349_3 (m.d 0 3) (by simp) with h18380 | h18380
                                        · linarith only [h17960, h18380, hlam]
                                        · rcases p18349_3 (m.d 0 4) (by simp) with h18382 | h18382
                                          · linarith only [h17961, h18382, hlam]
                                          · rcases p18349_3 (m.d 0 5) (by simp) with h18384 | h18384
                                            · linarith only [h17962, h18384, hlam]
                                            · rcases h2bigk with h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c | h18386c
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h0, hlam, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                rcases p18386_3 (m.d 0 2) (by simp) with h18389 | h18389
                                                · rcases p18386_3 (m.d 1 2) (by simp) with h18390 | h18390
                                                  · rcases p18386_3 (m.d 2 3) (by simp) with h18391 | h18391
                                                    · linarith only [h18391, hlam, p18386_0]
                                                    · rcases p18386_3 (m.d 2 4) (by simp) with h18393 | h18393
                                                      · linarith only [h17961, h18393, hlam]
                                                      · rcases p18386_3 (m.d 2 5) (by simp) with h18395 | h18395
                                                        · linarith only [h17962, h18395, hlam]
                                                        · linarith only [h18343, h18395, hlam]
                                                  · linarith only [h18335, h18390, hlam]
                                                · linarith only [h18389, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h14396, h16915, h17964, h18336, hlam, p18349_1, p18386_2]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                rcases p18386_3 (m.d 0 2) (by simp) with h18401 | h18401
                                                · rcases p18386_3 (m.d 1 2) (by simp) with h18402 | h18402
                                                  · rcases p18386_3 (m.d 2 3) (by simp) with h18403 | h18403
                                                    · linarith only [h17960, h18403, hlam]
                                                    · rcases p18386_3 (m.d 2 4) (by simp) with h18405 | h18405
                                                      · linarith only [h17961, h18405, hlam]
                                                      · rcases p18386_3 (m.d 2 5) (by simp) with h18407 | h18407
                                                        · linarith only [h18407, hlam, p18386_0]
                                                        · rcases h3bigk with h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c | h18409c
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h14396, hlam, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h0, h17964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18349_1, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h0, h17964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18349_1, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h17964, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h14396, hc01, hc13, hlam, hphi, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18335, h18342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            rcases p18409_3 (m.d 0 3) (by simp) with h18418 | h18418
                                                            · linarith only [h14396, h18418, hlam]
                                                            · linarith only [h17963, h18418, hlam]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h14396, h16915, h17964, h18335, h18336, h18342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h17960, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18335, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h17960, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18343, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h17963, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18338, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18342, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18347, hlam, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h14396, h16915, h18336, h18339, h18342, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18339, hlam, p18409_0]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18335, h18339, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [h18335, h18339, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18409_1]
                                                          · have p18409_0 := h18409c.1
                                                            have p18409_1 := h18409c.2.1
                                                            have p18409_2 := h18409c.2.2.1
                                                            have p18409_3 := h18409c.2.2.2
                                                            linarith only [hlam, p18409_0]
                                                  · linarith only [h18337, h18402, hlam]
                                                · linarith only [h18401, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h17960, h18342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                rcases p18386_3 (m.d 0 2) (by simp) with h18441 | h18441
                                                · linarith only [h0, h18441, hlam]
                                                · linarith only [h17960, h18441, hlam]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h0, h14396, h16915, h17964, h18336, hlam, p18349_1, p18386_2]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                rcases p18386_3 (m.d 0 2) (by simp) with h18445 | h18445
                                                · linarith only [h0, h18445, hlam]
                                                · linarith only [h17962, h18445, hlam]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h17960, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h18335, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h17960, h17964, h18342, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18349_1, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h18343, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h17961, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h18336, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h18342, hlam, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h18345, hlam, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h17962, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h18337, hlam, p18386_0]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h0, h17962, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18349_1, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [h0, h17962, h18342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18349_1, p18386_1]
                                              · have p18386_0 := h18386c.1
                                                have p18386_1 := h18386c.2.1
                                                have p18386_2 := h18386c.2.2.1
                                                have p18386_3 := h18386c.2.2.2
                                                linarith only [hlam, p18386_0]
                                      · linarith only [h17962, h18379, hlam]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h16915, h16916, h17964, h18336, h18340, h18342, hc34, hc45, hlam, hphi, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h17960, hlam, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h16915, h17964, h18335, h18336, h18339, h18342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h17964, hlam, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h16915, hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h17961, hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h17963, hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h18333, hlam, p18349_0]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h16915, h16916, h18336, h18340, h18342, hc34, hc45, hlam, hphi, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h17962, hlam, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [h14396, h16915, h17964, h18335, h18336, h18339, h18342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18349_1]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    rcases p18349_3 (m.d 0 1) (by simp) with h18477 | h18477
                                    · linarith only [h16916, h18477, hlam]
                                    · linarith only [h16915, h18477, hlam]
                                  · have p18349_0 := h18349c.1
                                    have p18349_1 := h18349c.2.1
                                    have p18349_2 := h18349c.2.2.1
                                    have p18349_3 := h18349c.2.2.2
                                    linarith only [hlam, p18349_0]
                          · linarith only [h17963, h17964, h18335, h18339, h18342, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18482 | h18482
                        · linarith only [h14396, h16915, h18339, h18482, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18484 | h18484
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18485 | h18485
                            · linarith only [h14396, h18339, h18485, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18487 | h18487
                              · linarith only [h14396, h16915, h18336, h18339, h18482, h18487, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18489 | h18489
                                · linarith only [h14396, h16915, h18336, h18339, h18482, h18484, h18489, hlam]
                                · linarith only [h14396, h16915, h18336, h18339, h18484, h18489, hc34, hc45, hlam, hphi]
                          · linarith only [h14396, h17963, h18339, h18484, hc23, hc35, hlam, hphi]
                    · linarith only [h14396, h16915, h17963, h18338, hlam]
                  · linarith only [h0, h17962, h18337, hlam]
                · linarith only [h0, h16915, h17961, h18336, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h17960, h18335, hlam]
        · linarith only [h14396, h16915, h17963, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18498 | h18498
        · rcases m.htr 0 3 5 (by decide) (by decide) with h18499 | h18499
          · linarith only [h17960, h17962, h18499, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18501 | h18501
            · linarith only [h0, h16915, h17962, h18501, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18503 | h18503
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18504 | h18504
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18505 | h18505
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18506 | h18506
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18507 | h18507
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18508 | h18508
                        · linarith only [h14396, h16915, h17960, h17962, h18501, h18505, h18508, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18510 | h18510
                          · linarith only [h17960, h17962, h18505, h18510, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h17960, h17962, h18498, h18505, h18510, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18513 | h18513
                        · linarith only [h14396, h16915, h17960, h17962, h18505, h18513, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18515 | h18515
                          · linarith only [h17960, h17962, h18505, h18515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h17960, h17962, h18498, h18505, h18515, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h14396, h16915, h18498, h18506, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18519 | h18519
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18520 | h18520
                      · linarith only [h14396, h16915, h18499, h18503, h18504, h18505, h18520, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18522 | h18522
                        · linarith only [h0, h16915, h18505, h18522, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18524 | h18524
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18525 | h18525
                            · linarith only [h0, h17960, h18505, h18520, h18525, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18527 | h18527
                              · linarith only [h14396, h16915, h16916, h17960, h17962, h18504, h18522, h18527, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h14396, h16915, h18503, h18505, h18527, hc14, hc45, hlam, hphi]
                          · linarith only [h14396, h18498, h18520, h18524, hc23, hc35, hlam, hphi]
                    · linarith only [h14396, h16915, h18498, h18519, hlam]
                · linarith only [h14396, h16915, h17961, h17962, h18503, h18504, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h17960, h18503, hlam]
        · linarith only [h14396, h16915, h18498, hlam]
    · linarith only [h0, h16915, h17961, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h18536 | h18536
    · rcases m.htr 0 2 5 (by decide) (by decide) with h18537 | h18537
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18538 | h18538
        · rcases m.htr 0 3 5 (by decide) (by decide) with h18539 | h18539
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18540 | h18540
            · linarith only [h16915, h16916, h18540, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18542 | h18542
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18543 | h18543
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18544 | h18544
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18545 | h18545
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18546 | h18546
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18547 | h18547
                        · linarith only [h16915, h16916, h17960, h18537, h18540, h18542, h18547, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18549 | h18549
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18550 | h18550
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18551 | h18551
                              · linarith only [h16915, h16916, h17960, h18537, h18542, h18543, h18547, h18551, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18553 | h18553
                                · linarith only [h16915, h16916, h18543, h18547, h18549, h18553, hlam]
                                · rcases h0bigk with h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c | h18555c
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h0, hlam, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h14396, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16916, h17960, h18537, h18542, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16916, hlam, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h17960, h18542, hc01, hc12, hlam, hphi, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h17960, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16915, h17960, h18542, h18543, h18549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h17960, h18542, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16915, h17960, h18542, h18543, h18549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h17960, h18537, h18542, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    rcases p18555_3 (m.d 0 1) (by simp) with h18569 | h18569
                                    · linarith only [h14396, h18569, hlam]
                                    · linarith only [h16915, h18569, hlam]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16915, h16916, h17960, h18542, h18543, h18549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16915, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h18536, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h18538, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h18540, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16915, h16916, h18543, h18547, h18549, hc34, hc45, hlam, hphi, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h18537, hlam, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h18539, hlam, p18555_0]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [h16915, h17960, h18537, h18542, h18543, h18549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18555_1]
                                  · have p18555_0 := h18555c.1
                                    have p18555_1 := h18555c.2.1
                                    have p18555_2 := h18555c.2.2.1
                                    have p18555_3 := h18555c.2.2.2
                                    linarith only [hlam, p18555_0]
                            · linarith only [h17960, h18539, h18550, hlam]
                          · linarith only [h17960, h18538, h18549, hlam]
                      · linarith only [h14396, h16915, h17960, h18537, h18539, h18543, h18546, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h14396, h18538, h18545, hlam]
                  · linarith only [h17960, h18542, h18544, hc02, hc25, hlam, hphi]
                · linarith only [h17960, h18542, h18543, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18589 | h18589
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18590 | h18590
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18591 | h18591
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18592 | h18592
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18593 | h18593
                        · linarith only [h16915, h16916, h18542, h18590, h18593, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18595 | h18595
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18596 | h18596
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18597 | h18597
                              · linarith only [h16915, h16916, h18589, h18593, h18597, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18599 | h18599
                                · linarith only [h16915, h16916, h18589, h18593, h18595, h18599, hlam]
                                · rcases h0bigk with h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c | h18601c
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h0, hlam, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h14396, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h16915, h16916, h18542, h18589, h18590, h18595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h16916, hlam, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h0, h18542, hc01, hc23, hlam, hphi, ht12, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h17960, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    rcases p18601_3 (m.d 0 1) (by simp) with h18610 | h18610
                                    · linarith only [h0, h18610, hlam]
                                    · linarith only [h16915, h18610, hlam]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h0, h16915, h16916, h18542, h18589, h18595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    rcases p18601_3 (m.d 0 1) (by simp) with h18614 | h18614
                                    · linarith only [h14396, h18614, hlam]
                                    · rcases p18601_3 (m.d 0 2) (by simp) with h18616 | h18616
                                      · linarith only [h17960, h18616, hlam]
                                      · linarith only [h0, h18616, hlam]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    rcases p18601_3 (m.d 0 1) (by simp) with h18619 | h18619
                                    · linarith only [h14396, h18619, hlam]
                                    · rcases p18601_3 (m.d 0 2) (by simp) with h18621 | h18621
                                      · linarith only [h17960, h18621, hlam]
                                      · rcases p18601_3 (m.d 0 3) (by simp) with h18623 | h18623
                                        · rcases p18601_3 (m.d 0 4) (by simp) with h18624 | h18624
                                          · linarith only [h18538, h18624, hlam]
                                          · rcases p18601_3 (m.d 0 5) (by simp) with h18626 | h18626
                                            · linarith only [h18539, h18626, hlam]
                                            · rcases h2bigk with h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c | h18628c
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h0, hlam, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h17960, hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h14396, h18542, h18595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18601_1, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h14396, h18542, h18595, h18597, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18601_1, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18542, hc02, hc23, hlam, hphi, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18542, hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                rcases p18628_3 (m.d 0 2) (by simp) with h18637 | h18637
                                                · linarith only [h0, h18637, hlam]
                                                · linarith only [h18536, h18637, hlam]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                rcases p18628_3 (m.d 0 2) (by simp) with h18640 | h18640
                                                · linarith only [h0, h18640, hlam]
                                                · linarith only [h18537, h18640, hlam]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                rcases p18628_3 (m.d 0 2) (by simp) with h18643 | h18643
                                                · linarith only [h18643, hlam, p18628_0]
                                                · rcases p18628_3 (m.d 1 2) (by simp) with h18645 | h18645
                                                  · linarith only [h18542, h18645, hlam]
                                                  · linarith only [h0, h18645, hlam]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h0, h16915, h18589, h18595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h14396, h16915, h16916, h18537, h18542, h18589, hlam, p18601_1, p18628_2]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h14396, h18537, h18542, hlam, p18601_1, p18628_2]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18536, hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18589, hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18595, hlam, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18597, hlam, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18537, hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18590, hlam, p18628_0]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18596, hlam, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [h18537, h18595, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18601_1, p18628_1]
                                              · have p18628_0 := h18628c.1
                                                have p18628_1 := h18628c.2.1
                                                have p18628_2 := h18628c.2.2.1
                                                have p18628_3 := h18628c.2.2.2
                                                linarith only [hlam, p18628_0]
                                        · linarith only [h17960, h18623, hlam]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    rcases p18601_3 (m.d 0 1) (by simp) with h18664 | h18664
                                    · linarith only [h14396, h18664, hlam]
                                    · linarith only [h16915, h18664, hlam]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    rcases p18601_3 (m.d 0 1) (by simp) with h18667 | h18667
                                    · linarith only [h14396, h18667, hlam]
                                    · rcases p18601_3 (m.d 0 2) (by simp) with h18669 | h18669
                                      · linarith only [h17960, h18669, hlam]
                                      · linarith only [h18537, h18669, hlam]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h16915, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h18536, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h18538, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h18540, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h16915, h16916, h18589, h18593, h18595, hc34, hc45, hlam, hphi, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h18537, hlam, p18601_1]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [h18539, hlam, p18601_0]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    rcases p18601_3 (m.d 0 1) (by simp) with h18680 | h18680
                                    · linarith only [h16916, h18680, hlam]
                                    · linarith only [h16915, h18680, hlam]
                                  · have p18601_0 := h18601c.1
                                    have p18601_1 := h18601c.2.1
                                    have p18601_2 := h18601c.2.2.1
                                    have p18601_3 := h18601c.2.2.2
                                    linarith only [hlam, p18601_0]
                            · linarith only [h0, h16915, h18542, h18589, h18595, h18596, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h16915, h16916, h18542, h18589, h18590, h18595, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h14396, h16915, h18537, h18539, h18542, h18589, h18592, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h14396, h16915, h17960, h18538, h18542, h18591, hc02, hc23, hlam, hphi]
                  · linarith only [h0, h16915, h18537, h18590, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h18536, h18589, hlam]
          · linarith only [h17960, h18537, h18539, hlam]
        · linarith only [h0, h16915, h17960, h18538, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18692 | h18692
        · rcases m.htr 0 3 5 (by decide) (by decide) with h18693 | h18693
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18694 | h18694
            · linarith only [h0, h16915, h18537, h18694, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18696 | h18696
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18697 | h18697
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18698 | h18698
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18699 | h18699
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18700 | h18700
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18701 | h18701
                        · linarith only [h0, h16915, h17960, h18694, h18696, h18701, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18703 | h18703
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18704 | h18704
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18705 | h18705
                              · linarith only [h0, h16915, h18537, h18697, h18698, h18701, h18705, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18707 | h18707
                                · linarith only [h0, h16915, h18537, h18697, h18698, h18701, h18703, h18707, hlam]
                                · rcases h0bigk with h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c | h18709c
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h0, hlam, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h14396, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h0, h18537, h18696, h18704, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h16916, hlam, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h18537, h18696, h18704, hc01, hc12, hlam, hphi, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h17960, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h16915, h18537, h18696, h18697, h18703, h18704, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h18537, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h16915, h17960, h18696, h18697, h18703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h0, h16915, h17960, h18696, h18697, h18703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    rcases p18709_3 (m.d 0 1) (by simp) with h18723 | h18723
                                    · linarith only [h14396, h18723, hlam]
                                    · linarith only [h16915, h18723, hlam]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h16915, h16916, h17960, h18696, h18697, h18703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h16915, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h18536, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h18692, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h18694, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h16915, h16916, h18697, h18701, h18703, hc34, hc45, hlam, hphi, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h0, h16915, h18537, h18696, h18697, h18703, h18704, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18709_1]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [h18693, hlam, p18709_0]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    rcases p18709_3 (m.d 0 1) (by simp) with h18735 | h18735
                                    · linarith only [h16916, h18735, hlam]
                                    · linarith only [h16915, h18735, hlam]
                                  · have p18709_0 := h18709c.1
                                    have p18709_1 := h18709c.2.1
                                    have p18709_2 := h18709c.2.2.1
                                    have p18709_3 := h18709c.2.2.2
                                    linarith only [hlam, p18709_0]
                            · linarith only [h17960, h18693, h18704, hlam]
                          · linarith only [h0, h16915, h17960, h18692, h18697, h18703, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h17960, h18693, h18696, h18700, hlam]
                    · linarith only [h17960, h18692, h18696, h18699, hlam]
                  · linarith only [h0, h17960, h18696, h18698, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h16915, h17960, h18696, h18697, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18745 | h18745
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18746 | h18746
                  · linarith only [h0, h16915, h18537, h18696, h18745, h18746, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18748 | h18748
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18749 | h18749
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18750 | h18750
                        · linarith only [h0, h16915, h18694, h18696, h18750, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18752 | h18752
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18753 | h18753
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18754 | h18754
                              · linarith only [h0, h16915, h18745, h18746, h18750, h18753, h18754, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h16915, h18745, h18746, h18752, h18754, hc34, hc45, hlam, hphi]
                            · linarith only [h14396, h18693, h18696, h18753, hlam]
                          · linarith only [h0, h16915, h18696, h18745, h18752, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h14396, h18693, h18749, hlam]
                    · linarith only [h14396, h18692, h18748, hlam]
                · linarith only [h0, h16915, h18536, h18745, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18762 | h18762
            · linarith only [h16915, h16916, h18762, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18764 | h18764
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18765 | h18765
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18766 | h18766
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18767 | h18767
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18768 | h18768
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18769 | h18769
                        · linarith only [h0, h16915, h18762, h18769, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18771 | h18771
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18772 | h18772
                            · linarith only [h0, h16915, h17960, h18693, h18764, h18765, h18771, h18772, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h16915, h17960, h18765, h18768, h18771, h18772, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h16915, h17960, h18692, h18693, h18771, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18776 | h18776
                        · linarith only [h14396, h16915, h18768, h18776, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18778 | h18778
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18779 | h18779
                            · linarith only [h18764, h18768, h18779, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18781 | h18781
                              · linarith only [h0, h16915, h17960, h18764, h18765, h18768, h18776, h18781, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18783 | h18783
                                · linarith only [h0, h16915, h17960, h18764, h18765, h18768, h18776, h18778, h18783, hlam]
                                · linarith only [h0, h16915, h17960, h18764, h18765, h18768, h18778, h18783, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h16915, h17960, h18692, h18765, h18778, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h14396, h16915, h18692, h18767, hlam]
                  · linarith only [h0, h17960, h18764, h18766, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h16915, h17960, h18764, h18765, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18790 | h18790
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18791 | h18791
                  · linarith only [h0, h16915, h18537, h18764, h18790, h18791, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18793 | h18793
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18794 | h18794
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18795 | h18795
                        · linarith only [h0, h16915, h18764, h18795, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18797 | h18797
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18798 | h18798
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18799 | h18799
                              · linarith only [h0, h16915, h17960, h18693, h18790, h18794, h18795, h18799, hlam]
                              · linarith only [h0, h16915, h18791, h18799, hc14, hc45, hlam, hphi]
                            · linarith only [h18764, h18794, h18798, hlam]
                          · linarith only [h0, h17960, h18693, h18764, h18794, h18797, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18804 | h18804
                        · linarith only [h0, h16915, h18764, h18804, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18806 | h18806
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18807 | h18807
                            · linarith only [h0, h16915, h18764, h18790, h18794, h18806, h18807, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h16915, h18764, h18790, h18806, h18807, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h16915, h18764, h18790, h18806, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h16915, h18692, h18764, h18790, h18793, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h18536, h18790, hlam]
        · linarith only [h14396, h16915, h18692, hlam]
    · linarith only [h0, h16915, h18536, hlam]

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h16916 | h16916
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  exact r1l7_10_12_23_L_I_L_I_H_I_s17 m hb0 hb2 hb3 h0 h14396 h16915

end R2N4
