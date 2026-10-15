import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6877 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6878 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h7954 | h7954
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7955 | h7955
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7956 | h7956
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7957 | h7957
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7958 | h7958
          · linarith only [h6874, h6878, h7958, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7960 | h7960
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7961 | h7961
              · linarith only [h0, h6874, h6878, h7955, h7958, h7961, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7963 | h7963
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7964 | h7964
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7965 | h7965
                    · rcases h2bigk with h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c | h7966c
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h0, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        rcases p7966_3 (m.d 0 2) (by simp) with h7969 | h7969
                        · rcases p7966_3 (m.d 1 2) (by simp) with h7970 | h7970
                          · rcases p7966_3 (m.d 2 3) (by simp) with h7971 | h7971
                            · linarith only [h7971, hlam, p7966_0]
                            · rcases p7966_3 (m.d 2 4) (by simp) with h7973 | h7973
                              · linarith only [h6876, h7973, hlam]
                              · linarith only [h7961, h7973, hlam]
                          · linarith only [h7955, h7970, hlam]
                        · linarith only [h7969, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        rcases p7966_3 (m.d 0 2) (by simp) with h7978 | h7978
                        · rcases p7966_3 (m.d 1 2) (by simp) with h7979 | h7979
                          · rcases p7966_3 (m.d 2 3) (by simp) with h7980 | h7980
                            · linarith only [h6875, h7980, hlam]
                            · rcases p7966_3 (m.d 2 4) (by simp) with h7982 | h7982
                              · linarith only [h7982, hlam, p7966_0]
                              · rcases p7966_3 (m.d 2 5) (by simp) with h7984 | h7984
                                · linarith only [h6877, h7984, hlam]
                                · rcases h4bigk with h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c | h7986c
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h0, h6874, h7958, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h0, h6874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h6878, hlam, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h6874, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h0, h6874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7958, hlam, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h6876, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7956, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7961, hlam, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7966_1, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h6875, h6878, h7963, h7965, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7955, h7958, h7963, h7965, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7961, h7963, h7965, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7986_1]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    rcases p7986_3 (m.d 0 4) (by simp) with h8006 | h8006
                                    · linarith only [h6878, h8006, hlam]
                                    · linarith only [h7954, h8006, hlam]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7954, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7960, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7964, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [h7965, hlam, p7986_0]
                                  · have p7986_0 := h7986c.1
                                    have p7986_1 := h7986c.2.1
                                    have p7986_2 := h7986c.2.2.1
                                    have p7986_3 := h7986c.2.2.2
                                    linarith only [hlam, p7986_0]
                          · linarith only [h7956, h7979, hlam]
                        · linarith only [h7978, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        rcases p7966_3 (m.d 0 2) (by simp) with h8016 | h8016
                        · rcases p7966_3 (m.d 1 2) (by simp) with h8017 | h8017
                          · rcases p7966_3 (m.d 2 3) (by simp) with h8018 | h8018
                            · linarith only [h6875, h8018, hlam]
                            · linarith only [h7963, h8018, hlam]
                          · linarith only [h7957, h8017, hlam]
                        · linarith only [h8016, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h0, h6874, h7955, h7958, h7963, h7965, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7966_1]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        rcases p7966_3 (m.d 0 2) (by simp) with h8025 | h8025
                        · linarith only [h0, h8025, hlam]
                        · linarith only [h6875, h8025, hlam]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        rcases p7966_3 (m.d 0 2) (by simp) with h8028 | h8028
                        · linarith only [h0, h8028, hlam]
                        · linarith only [h6876, h8028, hlam]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        rcases p7966_3 (m.d 0 2) (by simp) with h8031 | h8031
                        · linarith only [h0, h8031, hlam]
                        · linarith only [h6877, h8031, hlam]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h6875, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h7955, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h7961, hlam, p7966_1]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h0, h6874, h7955, h7958, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7966_1]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h6876, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h7956, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h6876, h7963, hc02, hc35, hlam, hphi, ht0b, ht5b, p7966_1]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h0, h6874, h7956, h7963, h7965, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7966_1]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h6877, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h7957, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h7963, hlam, p7966_0]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [h7964, hlam, p7966_1]
                      · have p7966_0 := h7966c.1
                        have p7966_1 := h7966c.2.1
                        have p7966_2 := h7966c.2.2.1
                        have p7966_3 := h7966c.2.2.2
                        linarith only [hlam, p7966_0]
                    · linarith only [h0, h6874, h6875, h6878, h7954, h7963, h7965, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h6874, h7960, h7964, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8051 | h8051
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8052 | h8052
                    · rcases h2bigk with h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h0, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        rcases p8053_3 (m.d 0 2) (by simp) with h8056 | h8056
                        · rcases p8053_3 (m.d 1 2) (by simp) with h8057 | h8057
                          · rcases p8053_3 (m.d 2 3) (by simp) with h8058 | h8058
                            · linarith only [h8058, hlam, p8053_0]
                            · rcases p8053_3 (m.d 2 4) (by simp) with h8060 | h8060
                              · linarith only [h6876, h8060, hlam]
                              · linarith only [h7961, h8060, hlam]
                          · linarith only [h7955, h8057, hlam]
                        · linarith only [h8056, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        rcases p8053_3 (m.d 0 2) (by simp) with h8065 | h8065
                        · rcases p8053_3 (m.d 1 2) (by simp) with h8066 | h8066
                          · rcases p8053_3 (m.d 2 3) (by simp) with h8067 | h8067
                            · linarith only [h6875, h8067, hlam]
                            · rcases p8053_3 (m.d 2 4) (by simp) with h8069 | h8069
                              · linarith only [h8069, hlam, p8053_0]
                              · rcases p8053_3 (m.d 2 5) (by simp) with h8071 | h8071
                                · linarith only [h6877, h8071, hlam]
                                · rcases h4bigk with h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h0, h6874, h7963, h8051, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h6878, hlam, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h6874, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h8051, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7958, hlam, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h6876, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7956, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7961, hlam, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8053_1, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h6877, h7954, h7963, hc23, hc34, hlam, hphi, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7957, h7960, h7963, hc23, hc34, hlam, hphi, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7961, hc23, hc34, hlam, hphi, p8073_1]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    rcases p8073_3 (m.d 0 4) (by simp) with h8093 | h8093
                                    · linarith only [h6878, h8093, hlam]
                                    · linarith only [h7954, h8093, hlam]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7954, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h7960, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h8051, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [h8052, hlam, p8073_0]
                                  · have p8073_0 := h8073c.1
                                    have p8073_1 := h8073c.2.1
                                    have p8073_2 := h8073c.2.2.1
                                    have p8073_3 := h8073c.2.2.2
                                    linarith only [hlam, p8073_0]
                          · linarith only [h7956, h8066, hlam]
                        · linarith only [h8065, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        rcases p8053_3 (m.d 0 2) (by simp) with h8103 | h8103
                        · rcases p8053_3 (m.d 1 2) (by simp) with h8104 | h8104
                          · rcases p8053_3 (m.d 2 3) (by simp) with h8105 | h8105
                            · linarith only [h6875, h8105, hlam]
                            · rcases p8053_3 (m.d 2 4) (by simp) with h8107 | h8107
                              · linarith only [h6876, h8107, hlam]
                              · linarith only [h8051, h8107, hlam]
                          · linarith only [h7957, h8104, hlam]
                        · linarith only [h8103, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h0, h6874, h7956, h8051, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        rcases p8053_3 (m.d 0 2) (by simp) with h8114 | h8114
                        · linarith only [h0, h8114, hlam]
                        · linarith only [h6875, h8114, hlam]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        rcases p8053_3 (m.d 0 2) (by simp) with h8117 | h8117
                        · linarith only [h0, h8117, hlam]
                        · linarith only [h6876, h8117, hlam]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        rcases p8053_3 (m.d 0 2) (by simp) with h8120 | h8120
                        · linarith only [h0, h8120, hlam]
                        · linarith only [h6877, h8120, hlam]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h6875, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h7955, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h7961, hlam, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h7963, hlam, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h6876, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h7956, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h0, h6874, h7956, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h0, h6874, h7956, h7963, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h6877, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h7957, hlam, p8053_0]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h0, h6874, h7957, h7960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [h8051, hlam, p8053_1]
                      · have p8053_0 := h8053c.1
                        have p8053_1 := h8053c.2.1
                        have p8053_2 := h8053c.2.2.1
                        have p8053_3 := h8053c.2.2.2
                        linarith only [hlam, p8053_0]
                    · linarith only [h6878, h7954, h8052, hlam]
                  · linarith only [h0, h6874, h7960, h8051, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8140 | h8140
              · linarith only [h6875, h6878, h7954, h7960, h8140, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8142 | h8142
                · linarith only [h0, h6874, h7954, h7955, h7958, h7960, h8142, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8144 | h8144
                  · linarith only [h7956, h7960, h8144, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8146 | h8146
                    · rcases h2bigk with h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c | h8147c
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h0, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        rcases p8147_3 (m.d 0 2) (by simp) with h8150 | h8150
                        · rcases p8147_3 (m.d 1 2) (by simp) with h8151 | h8151
                          · rcases p8147_3 (m.d 2 3) (by simp) with h8152 | h8152
                            · linarith only [h8152, hlam, p8147_0]
                            · rcases p8147_3 (m.d 2 4) (by simp) with h8154 | h8154
                              · linarith only [h6876, h8154, hlam]
                              · linarith only [h8140, h8154, hlam]
                          · linarith only [h7955, h8151, hlam]
                        · linarith only [h8150, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        rcases p8147_3 (m.d 0 2) (by simp) with h8159 | h8159
                        · rcases p8147_3 (m.d 1 2) (by simp) with h8160 | h8160
                          · rcases p8147_3 (m.d 2 3) (by simp) with h8161 | h8161
                            · linarith only [h6875, h8161, hlam]
                            · rcases p8147_3 (m.d 2 4) (by simp) with h8163 | h8163
                              · linarith only [h8163, hlam, p8147_0]
                              · rcases p8147_3 (m.d 2 5) (by simp) with h8165 | h8165
                                · linarith only [h6877, h8165, hlam]
                                · linarith only [h8144, h8165, hlam]
                          · linarith only [h7956, h8160, hlam]
                        · linarith only [h8159, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        rcases p8147_3 (m.d 0 2) (by simp) with h8170 | h8170
                        · rcases p8147_3 (m.d 1 2) (by simp) with h8171 | h8171
                          · rcases p8147_3 (m.d 2 3) (by simp) with h8172 | h8172
                            · linarith only [h6875, h8172, hlam]
                            · rcases p8147_3 (m.d 2 4) (by simp) with h8174 | h8174
                              · linarith only [h6876, h8174, hlam]
                              · rcases p8147_3 (m.d 2 5) (by simp) with h8176 | h8176
                                · linarith only [h8176, hlam, p8147_0]
                                · rcases h4bigk with h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c | h8178c
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h0, h6874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h6878, hlam, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h0, h6874, h7960, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h6874, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h0, h6874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7958, hlam, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7960, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h6876, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7956, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h8140, hlam, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h8144, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h6878, hc03, hc34, hlam, hphi, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7955, h7958, hc23, hc34, hlam, hphi, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h8140, hc23, hc34, hlam, hphi, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7955, h7958, h7960, hc23, hc34, hlam, hphi, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7954, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h7954, h7955, h7958, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h0, h6874, h7954, h8140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8178_1]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [h8146, hlam, p8178_0]
                                  · have p8178_0 := h8178c.1
                                    have p8178_1 := h8178c.2.1
                                    have p8178_2 := h8178c.2.2.1
                                    have p8178_3 := h8178c.2.2.2
                                    linarith only [hlam, p8178_0]
                          · linarith only [h7957, h8171, hlam]
                        · linarith only [h8170, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h0, h6874, h7954, h7955, h7958, h7960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8147_1]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h0, h6874, h7954, h7955, h7958, h7960, hlam, p8147_2]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h0, h6874, h7954, h7956, h7960, hlam, p8147_2]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        rcases p8147_3 (m.d 0 2) (by simp) with h8210 | h8210
                        · linarith only [h0, h8210, hlam]
                        · linarith only [h6877, h8210, hlam]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h6875, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h7955, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h8140, hlam, p8147_1]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h8142, hlam, p8147_1]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h6876, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h7956, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h6874, h7954, h7956, h7960, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8147_1]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h8144, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h6877, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h7957, hlam, p8147_0]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h0, h6874, h7954, h7957, h7960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8147_1]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [h0, h6874, h7954, h7957, h7960, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8147_1]
                      · have p8147_0 := h8147c.1
                        have p8147_1 := h8147c.2.1
                        have p8147_2 := h8147c.2.2.1
                        have p8147_3 := h8147c.2.2.2
                        linarith only [hlam, p8147_0]
                    · linarith only [h0, h6874, h6875, h6878, h7954, h8146, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h6874, h6877, h7954, h7957, hc02, hc45, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h6876, h7956, hlam]
    · linarith only [h0, h6874, h6875, h6878, h7954, h7955, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8232 | h8232
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8233 | h8233
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8234 | h8234
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8235 | h8235
          · linarith only [h6874, h6878, h8235, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8237 | h8237
            · linarith only [h6874, h7954, h8237, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8239 | h8239
              · linarith only [h6875, h6878, h8239, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8241 | h8241
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8242 | h8242
                  · linarith only [h6876, h7954, h8242, hlam]
                  · linarith only [h8239, h8241, h8242, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8245 | h8245
                  · linarith only [h6876, h7954, h8245, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8247 | h8247
                    · rcases h2bigk with h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c | h8248c
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h0, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8251 | h8251
                        · rcases p8248_3 (m.d 1 2) (by simp) with h8252 | h8252
                          · rcases p8248_3 (m.d 2 3) (by simp) with h8253 | h8253
                            · linarith only [h8253, hlam, p8248_0]
                            · rcases p8248_3 (m.d 2 4) (by simp) with h8255 | h8255
                              · linarith only [h6876, h8255, hlam]
                              · linarith only [h8239, h8255, hlam]
                          · linarith only [h8232, h8252, hlam]
                        · linarith only [h8251, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8260 | h8260
                        · rcases p8248_3 (m.d 1 2) (by simp) with h8261 | h8261
                          · rcases p8248_3 (m.d 2 3) (by simp) with h8262 | h8262
                            · linarith only [h6875, h8262, hlam]
                            · rcases p8248_3 (m.d 2 4) (by simp) with h8264 | h8264
                              · linarith only [h8264, hlam, p8248_0]
                              · rcases p8248_3 (m.d 2 5) (by simp) with h8266 | h8266
                                · linarith only [h6877, h8266, hlam]
                                · linarith only [h8245, h8266, hlam]
                          · linarith only [h8233, h8261, hlam]
                        · linarith only [h8260, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8271 | h8271
                        · rcases p8248_3 (m.d 1 2) (by simp) with h8272 | h8272
                          · rcases p8248_3 (m.d 2 3) (by simp) with h8273 | h8273
                            · linarith only [h6875, h8273, hlam]
                            · rcases p8248_3 (m.d 2 4) (by simp) with h8275 | h8275
                              · linarith only [h6876, h8275, hlam]
                              · rcases p8248_3 (m.d 2 5) (by simp) with h8277 | h8277
                                · linarith only [h8277, hlam, p8248_0]
                                · rcases h4bigk with h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c | h8279c
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h7954, h8235, h8247, hc13, hc34, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h7954, h8239, h8247, hc23, hc34, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h6878, hlam, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h7954, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h6874, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8235, hlam, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8237, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h6876, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8233, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8239, hlam, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8245, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h6876, h8239, hc23, hc34, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc34, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8239, hc23, hc34, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h6874, h7954, h8233, h8239, hc23, hc34, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h6874, h8233, h8239, h8247, hc23, hc35, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8233, h8239, h8247, hc23, hc35, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8239, h8247, hc23, hc35, hlam, hphi, p8279_1]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [h8247, hlam, p8279_0]
                                  · have p8279_0 := h8279c.1
                                    have p8279_1 := h8279c.2.1
                                    have p8279_2 := h8279c.2.2.1
                                    have p8279_3 := h8279c.2.2.2
                                    linarith only [hlam, p8279_0]
                          · linarith only [h8234, h8272, hlam]
                        · linarith only [h8271, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8307 | h8307
                        · linarith only [h0, h8307, hlam]
                        · rcases p8248_3 (m.d 1 2) (by simp) with h8309 | h8309
                          · rcases p8248_3 (m.d 2 3) (by simp) with h8310 | h8310
                            · linarith only [h8232, h8310, hlam]
                            · rcases p8248_3 (m.d 2 4) (by simp) with h8312 | h8312
                              · linarith only [h8233, h8312, hlam]
                              · rcases p8248_3 (m.d 2 5) (by simp) with h8314 | h8314
                                · linarith only [h8234, h8314, hlam]
                                · rcases h4bigk with h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c | h8316c
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h0, h6874, h8233, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8248_1, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8248_1, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h6878, hlam, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h7954, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h6874, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8248_1, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8235, hlam, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8237, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h6876, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8233, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8239, hlam, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8245, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h6876, h8239, hc23, hc34, hlam, hphi, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc34, hlam, hphi, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8239, hc23, hc34, hlam, hphi, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h6874, h7954, h8233, h8239, hc23, hc34, hlam, hphi, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h6874, h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8239, hc23, hc45, hlam, hphi, ht34, p8316_1]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [h8247, hlam, p8316_0]
                                  · have p8316_0 := h8316c.1
                                    have p8316_1 := h8316c.2.1
                                    have p8316_2 := h8316c.2.2.1
                                    have p8316_3 := h8316c.2.2.2
                                    linarith only [hlam, p8316_0]
                          · linarith only [h0, h8309, hlam]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8344 | h8344
                        · linarith only [h0, h8344, hlam]
                        · linarith only [h6875, h8344, hlam]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8347 | h8347
                        · linarith only [h0, h8347, hlam]
                        · linarith only [h6876, h8347, hlam]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        rcases p8248_3 (m.d 0 2) (by simp) with h8350 | h8350
                        · linarith only [h0, h8350, hlam]
                        · linarith only [h6877, h8350, hlam]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h6875, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h8232, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h8239, hlam, p8248_1]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h8241, hlam, p8248_1]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h6876, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h8233, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h0, h6874, h8233, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8248_1]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h8245, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h6877, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h8234, hlam, p8248_0]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h6877, h7954, h8247, hc23, hc34, hlam, hphi, p8248_1]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [h6877, h7954, h8239, h8247, hc23, hc34, hlam, hphi, p8248_1]
                      · have p8248_0 := h8248c.1
                        have p8248_1 := h8248c.2.1
                        have p8248_2 := h8248c.2.2.1
                        have p8248_3 := h8248c.2.2.2
                        linarith only [hlam, p8248_0]
                    · rcases h2bigk with h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c | h8368c
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h0, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8371 | h8371
                        · rcases p8368_3 (m.d 1 2) (by simp) with h8372 | h8372
                          · rcases p8368_3 (m.d 2 3) (by simp) with h8373 | h8373
                            · linarith only [h8373, hlam, p8368_0]
                            · rcases p8368_3 (m.d 2 4) (by simp) with h8375 | h8375
                              · linarith only [h6876, h8375, hlam]
                              · linarith only [h8239, h8375, hlam]
                          · linarith only [h8232, h8372, hlam]
                        · linarith only [h8371, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8380 | h8380
                        · rcases p8368_3 (m.d 1 2) (by simp) with h8381 | h8381
                          · rcases p8368_3 (m.d 2 3) (by simp) with h8382 | h8382
                            · linarith only [h6875, h8382, hlam]
                            · rcases p8368_3 (m.d 2 4) (by simp) with h8384 | h8384
                              · linarith only [h8384, hlam, p8368_0]
                              · rcases p8368_3 (m.d 2 5) (by simp) with h8386 | h8386
                                · linarith only [h6877, h8386, hlam]
                                · linarith only [h8245, h8386, hlam]
                          · linarith only [h8233, h8381, hlam]
                        · linarith only [h8380, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8391 | h8391
                        · rcases p8368_3 (m.d 1 2) (by simp) with h8392 | h8392
                          · rcases p8368_3 (m.d 2 3) (by simp) with h8393 | h8393
                            · linarith only [h6875, h8393, hlam]
                            · rcases p8368_3 (m.d 2 4) (by simp) with h8395 | h8395
                              · linarith only [h6876, h8395, hlam]
                              · rcases p8368_3 (m.d 2 5) (by simp) with h8397 | h8397
                                · linarith only [h8397, hlam, p8368_0]
                                · rcases h4bigk with h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c | h8399c
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6878, h8247, hc14, hc45, hlam, hphi, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6878, h8239, h8247, hc23, hc45, hlam, hphi, ht34, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6878, hlam, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h7954, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6874, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6874, h8239, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8235, hlam, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8237, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6876, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8233, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8239, hlam, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8245, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8247, hc04, hc45, hlam, hphi, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8247, hc14, hc45, hlam, hphi, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8239, h8247, hc23, hc45, hlam, hphi, ht34, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8247, hlam, p8399_0]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h6874, h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [h8239, hc23, hc45, hlam, hphi, ht34, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [hc34, hc45, hlam, hphi, p8399_1]
                                  · have p8399_0 := h8399c.1
                                    have p8399_1 := h8399c.2.1
                                    have p8399_2 := h8399c.2.2.1
                                    have p8399_3 := h8399c.2.2.2
                                    linarith only [hlam, p8399_0]
                          · linarith only [h8234, h8392, hlam]
                        · linarith only [h8391, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8427 | h8427
                        · linarith only [h0, h8427, hlam]
                        · rcases p8368_3 (m.d 1 2) (by simp) with h8429 | h8429
                          · rcases p8368_3 (m.d 2 3) (by simp) with h8430 | h8430
                            · linarith only [h8232, h8430, hlam]
                            · rcases p8368_3 (m.d 2 4) (by simp) with h8432 | h8432
                              · linarith only [h8233, h8432, hlam]
                              · rcases p8368_3 (m.d 2 5) (by simp) with h8434 | h8434
                                · linarith only [h8234, h8434, hlam]
                                · rcases h4bigk with h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c | h8436c
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h0, h6874, h8233, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8368_1, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8368_1, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h6878, hlam, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h7954, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h6874, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8368_1, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8235, hlam, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8237, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h6876, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8233, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8239, hlam, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8245, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h6876, h8239, hc23, hc34, hlam, hphi, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc34, hlam, hphi, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8239, hc23, hc34, hlam, hphi, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8247, hlam, p8436_0]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h6874, h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [h8239, hc23, hc45, hlam, hphi, ht34, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [hc34, hc45, hlam, hphi, p8436_1]
                                  · have p8436_0 := h8436c.1
                                    have p8436_1 := h8436c.2.1
                                    have p8436_2 := h8436c.2.2.1
                                    have p8436_3 := h8436c.2.2.2
                                    linarith only [hlam, p8436_0]
                          · linarith only [h0, h8429, hlam]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8464 | h8464
                        · linarith only [h0, h8464, hlam]
                        · linarith only [h6875, h8464, hlam]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8467 | h8467
                        · linarith only [h0, h8467, hlam]
                        · linarith only [h6876, h8467, hlam]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8470 | h8470
                        · linarith only [h0, h8470, hlam]
                        · linarith only [h6877, h8470, hlam]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h6875, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h8232, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h8239, hlam, p8368_1]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h8241, hlam, p8368_1]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h6876, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h8233, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h0, h6874, h8233, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8368_1]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h8245, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h6877, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [h8234, hlam, p8368_0]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8485 | h8485
                        · rcases p8368_3 (m.d 1 2) (by simp) with h8486 | h8486
                          · rcases p8368_3 (m.d 2 3) (by simp) with h8487 | h8487
                            · linarith only [h8241, h8487, hlam]
                            · rcases p8368_3 (m.d 2 4) (by simp) with h8489 | h8489
                              · linarith only [h8245, h8489, hlam]
                              · linarith only [h8239, h8489, hlam]
                          · linarith only [h8232, h8486, hlam]
                        · linarith only [h6875, h8485, hlam]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        rcases p8368_3 (m.d 0 2) (by simp) with h8494 | h8494
                        · rcases p8368_3 (m.d 1 2) (by simp) with h8495 | h8495
                          · rcases p8368_3 (m.d 2 3) (by simp) with h8496 | h8496
                            · linarith only [h8241, h8496, hlam]
                            · rcases p8368_3 (m.d 2 4) (by simp) with h8498 | h8498
                              · linarith only [h8245, h8498, hlam]
                              · rcases p8368_3 (m.d 2 5) (by simp) with h8500 | h8500
                                · rcases h4bigk with h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h6878, hlam, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h7954, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h6874, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h0, h6874, h8239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8235, hlam, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8237, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h6876, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8233, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8239, hlam, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8245, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h6876, h8239, hc23, hc34, hlam, hphi, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc34, hlam, hphi, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8239, hc23, hc34, hlam, hphi, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8247, hlam, p8501_0]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h6874, h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8233, h8239, hc23, hc45, hlam, hphi, ht34, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [h8239, hc23, hc45, hlam, hphi, ht34, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [hc34, hc45, hlam, hphi, p8501_1]
                                  · have p8501_0 := h8501c.1
                                    have p8501_1 := h8501c.2.1
                                    have p8501_2 := h8501c.2.2.1
                                    have p8501_3 := h8501c.2.2.2
                                    linarith only [hlam, p8501_0]
                                · linarith only [h8245, h8500, hlam]
                          · linarith only [h8233, h8495, hlam]
                        · linarith only [h6876, h8494, hlam]
                      · have p8368_0 := h8368c.1
                        have p8368_1 := h8368c.2.1
                        have p8368_2 := h8368c.2.2.1
                        have p8368_3 := h8368c.2.2.2
                        linarith only [hlam, p8368_0]
        · linarith only [h0, h6877, h8234, hlam]
      · linarith only [h0, h6876, h8233, hlam]
    · linarith only [h0, h6874, h6875, h6878, h8232, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6877 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h6878 | h6878
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x0 m hb2 hb4 hg0 h6874 h6875 h6876 h6877 h6878
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x1 m hb2 hb4 hg0 h6874 h6875 h6876 h6877 h6878

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6877 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h8534 | h8534
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8535 | h8535
    · linarith only [h0, h6874, h6877, h8535, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8537 | h8537
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8538 | h8538
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8539 | h8539
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8540 | h8540
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8541 | h8541
              · linarith only [h0, h6874, h6877, h8535, h8539, h8541, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8543 | h8543
                · linarith only [h6875, h6877, h8539, h8543, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h6875, h6877, h8534, h8539, h8543, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h6875, h6877, h8534, h8539, h8540, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8547 | h8547
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8548 | h8548
              · linarith only [h0, h6874, h8539, h8548, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8550 | h8550
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8551 | h8551
                  · linarith only [h0, h6874, h6875, h8539, h8551, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8553 | h8553
                    · linarith only [h0, h6874, h8535, h8538, h8539, h8551, h8553, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h6874, h8539, h8553, hc14, hc45, hlam, hphi]
                · linarith only [h0, h6874, h8539, h8547, h8550, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8557 | h8557
              · linarith only [h0, h6874, h8539, h8557, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8559 | h8559
                · linarith only [h8537, h8547, h8559, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8561 | h8561
                  · linarith only [h0, h6874, h8534, h8537, h8539, h8547, h8561, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h6874, h8534, h8537, h8539, h8547, h8561, hc23, hc35, hlam, hphi]
        · linarith only [h0, h6876, h8538, hlam]
      · linarith only [h0, h6875, h8537, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8566 | h8566
    · linarith only [h0, h6874, h6877, h8566, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8568 | h8568
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8569 | h8569
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8570 | h8570
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8571 | h8571
            · linarith only [h0, h6874, h6875, h6877, h8534, h8570, h8571, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8573 | h8573
              · linarith only [h0, h6874, h6877, h8570, h8573, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8575 | h8575
                · linarith only [h6875, h8534, h8575, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8577 | h8577
                  · linarith only [h6875, h6877, h8570, h8577, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8579 | h8579
                    · linarith only [h0, h6874, h6877, h8569, h8570, h8573, h8579, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8581 | h8581
                      · linarith only [h0, h6874, h6877, h8570, h8571, h8573, h8581, hc13, hc34, hlam, hphi]
                      · rcases h2bigk with h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c | h8583c
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h0, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6877, h8570, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6877, h8570, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6877, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          rcases p8583_3 (m.d 0 2) (by simp) with h8589 | h8589
                          · linarith only [h0, h8589, hlam]
                          · rcases p8583_3 (m.d 1 2) (by simp) with h8591 | h8591
                            · rcases p8583_3 (m.d 2 3) (by simp) with h8592 | h8592
                              · linarith only [h8568, h8592, hlam]
                              · rcases p8583_3 (m.d 2 4) (by simp) with h8594 | h8594
                                · linarith only [h8569, h8594, hlam]
                                · rcases p8583_3 (m.d 2 5) (by simp) with h8596 | h8596
                                  · linarith only [h8570, h8596, hlam]
                                  · linarith only [h6877, h8596, hlam]
                            · linarith only [h0, h8591, hlam]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6875, h6877, h8570, hlam, p8583_2]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6876, h6877, h8570, hlam, p8583_2]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h0, h6877, hc01, hc12, hlam, hphi, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6875, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h8568, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h8575, hlam, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h8577, hlam, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6876, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h8569, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h0, h6874, h6877, h8569, h8570, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h8579, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h6875, h8577, hc23, hc35, hlam, hphi, p8583_1]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [h8570, hlam, p8583_0]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          rcases p8583_3 (m.d 0 2) (by simp) with h8616 | h8616
                          · linarith only [h6877, h8616, hlam]
                          · linarith only [h6875, h8616, hlam]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          rcases p8583_3 (m.d 0 2) (by simp) with h8619 | h8619
                          · linarith only [h6877, h8619, hlam]
                          · linarith only [h6876, h8619, hlam]
                        · have p8583_0 := h8583c.1
                          have p8583_1 := h8583c.2.1
                          have p8583_2 := h8583c.2.2.1
                          have p8583_3 := h8583c.2.2.2
                          linarith only [hlam, p8583_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8623 | h8623
            · linarith only [h0, h6874, h6875, h8534, h8570, h8623, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8625 | h8625
              · linarith only [h0, h6874, h8570, h8625, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8627 | h8627
                · linarith only [h6875, h8534, h8627, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8629 | h8629
                  · linarith only [h0, h6874, h8568, h8570, h8623, h8629, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h6874, h8568, h8570, h8623, h8629, hc23, hc35, hlam, hphi]
        · linarith only [h0, h6874, h6876, h6877, h8569, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h0, h6875, h8568, hlam]

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h6877 | h6877
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0 m hb2 hb4 hg0 h6874 h6875 h6876 h6877
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x1 m hb2 hb4 hg0 h6874 h6875 h6876 h6877

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  linarith only [h0, h6874, h6876, hlam]

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h6876 | h6876
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0 m hb2 hb4 hg0 h6874 h6875 h6876
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x1 m hb2 hb4 hg0 h6874 h6875 h6876

end R2N4
