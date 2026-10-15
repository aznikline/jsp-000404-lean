import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S11
import Jsp000404.R1LeavesN7_2S18
import Jsp000404.R1LeavesN7_2S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11162000 in
set_option maxHeartbeats 11162000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s10_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7337 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7338 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h7987 | h7987
  · rcases m.htr 0 3 5 (by decide) (by decide) with h7988 | h7988
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7989 | h7989
      · linarith only [h7337, h7338, h7989, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7991 | h7991
        · linarith only [h0, h4, h7337, h7991, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7993 | h7993
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7994 | h7994
            · linarith only [h0, h7338, h7994, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7996 | h7996
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7997 | h7997
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7998 | h7998
                  · linarith only [h2, h7989, h7998, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8000 | h8000
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8001 | h8001
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8002 | h8002
                        · linarith only [h0, h2, h7338, h7989, h7993, h8001, h8002, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8004 | h8004
                          · linarith only [h7337, h7338, h8000, h8002, h8004, hlam]
                          · rcases h0bigk with h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c | h8006c
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8008 | h8008
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8009 | h8009
                                · linarith only [h0, h8009, hlam]
                                · rcases p8006_3 (m.d 0 3) (by simp) with h8011 | h8011
                                  · linarith only [h1, h8011, hlam]
                                  · linarith only [h4, h8011, hlam]
                              · linarith only [h0, h8008, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8015 | h8015
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8016 | h8016
                                · linarith only [h0, h8016, hlam]
                                · rcases p8006_3 (m.d 0 3) (by simp) with h8018 | h8018
                                  · linarith only [h1, h8018, hlam]
                                  · rcases p8006_3 (m.d 0 4) (by simp) with h8020 | h8020
                                    · linarith only [h2, h8020, hlam]
                                    · rcases p8006_3 (m.d 0 5) (by simp) with h8022 | h8022
                                      · linarith only [h3, h8022, hlam]
                                      · rcases h2bigk with h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7338, h7993, h8000, h8001, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h4, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7338, h7988, h8000, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8006_1, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7338, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h0, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7991, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h0, h7338, h7988, h8000, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8006_1, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7994, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          rcases p8024_3 (m.d 0 2) (by simp) with h8035 | h8035
                                          · linarith only [h8035, hlam, p8024_0]
                                          · rcases p8024_3 (m.d 1 2) (by simp) with h8037 | h8037
                                            · linarith only [h7991, h8037, hlam]
                                            · rcases p8024_3 (m.d 2 3) (by simp) with h8039 | h8039
                                              · rcases p8024_3 (m.d 2 4) (by simp) with h8040 | h8040
                                                · linarith only [h8000, h8040, hlam]
                                                · rcases p8024_3 (m.d 2 5) (by simp) with h8042 | h8042
                                                  · linarith only [h8001, h8042, hlam]
                                                  · linarith only [h7338, h8042, hlam]
                                              · linarith only [h8039, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          rcases p8024_3 (m.d 0 2) (by simp) with h8046 | h8046
                                          · linarith only [h4, h8046, hlam]
                                          · linarith only [h0, h8046, hlam]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          rcases p8024_3 (m.d 0 2) (by simp) with h8050 | h8050
                                          · linarith only [h4, h8050, hlam]
                                          · linarith only [h7337, h8050, hlam]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7338, hc02, hc23, hlam, hphi, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7337, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7993, hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h8000, hlam, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [hlam, p8024_0]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h8002, hlam, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h0, h7993, h8000, h8002, hc34, hc45, hlam, hphi, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h7993, h8000, h8002, hc34, hc45, hlam, hphi, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [h8001, hlam, p8024_1]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          rcases p8024_3 (m.d 0 2) (by simp) with h8062 | h8062
                                          · linarith only [h7338, h8062, hlam]
                                          · linarith only [h7337, h8062, hlam]
                                        · have p8024_0 := h8024c.1
                                          have p8024_1 := h8024c.2.1
                                          have p8024_2 := h8024c.2.2.1
                                          have p8024_3 := h8024c.2.2.2
                                          linarith only [hlam, p8024_0]
                              · linarith only [h1, h8015, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8067 | h8067
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8068 | h8068
                                · linarith only [h0, h8068, hlam]
                                · linarith only [h7337, h8068, hlam]
                              · linarith only [h2, h8067, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8072 | h8072
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8073 | h8073
                                · linarith only [h0, h8073, hlam]
                                · rcases p8006_3 (m.d 0 3) (by simp) with h8075 | h8075
                                  · linarith only [h1, h8075, hlam]
                                  · linarith only [h7988, h8075, hlam]
                              · linarith only [h3, h8072, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h0, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h4, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h7337, h7338, h8000, h8002, hc34, hc45, hlam, hphi, p8006_1]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h7338, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h1, hlam, p8006_1]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8085 | h8085
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8086 | h8086
                                · linarith only [h4, h8086, hlam]
                                · rcases p8006_3 (m.d 0 3) (by simp) with h8088 | h8088
                                  · rcases p8006_3 (m.d 0 4) (by simp) with h8089 | h8089
                                    · linarith only [h7987, h8089, hlam]
                                    · rcases p8006_3 (m.d 0 5) (by simp) with h8091 | h8091
                                      · linarith only [h7988, h8091, hlam]
                                      · linarith only [h7338, h8091, hlam]
                                  · linarith only [h4, h8088, hlam]
                              · linarith only [h0, h8085, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8097 | h8097
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8098 | h8098
                                · linarith only [h4, h8098, hlam]
                                · linarith only [h7337, h8098, hlam]
                              · linarith only [h2, h8097, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8102 | h8102
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8103 | h8103
                                · linarith only [h4, h8103, hlam]
                                · rcases p8006_3 (m.d 0 3) (by simp) with h8105 | h8105
                                  · rcases p8006_3 (m.d 0 4) (by simp) with h8106 | h8106
                                    · linarith only [h7987, h8106, hlam]
                                    · rcases p8006_3 (m.d 0 5) (by simp) with h8108 | h8108
                                      · linarith only [h7988, h8108, hlam]
                                      · rcases h2bigk with h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c | h8110c
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h4, h7338, h7993, h8000, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8006_1, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h4, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h4, h7338, h8000, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8006_1, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7338, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h0, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7991, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h0, h4, h7338, h8000, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8006_1, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7994, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          rcases p8110_3 (m.d 0 2) (by simp) with h8121 | h8121
                                          · linarith only [h8121, hlam, p8110_0]
                                          · rcases p8110_3 (m.d 1 2) (by simp) with h8123 | h8123
                                            · linarith only [h7991, h8123, hlam]
                                            · rcases p8110_3 (m.d 2 3) (by simp) with h8125 | h8125
                                              · rcases p8110_3 (m.d 2 4) (by simp) with h8126 | h8126
                                                · linarith only [h8000, h8126, hlam]
                                                · rcases p8110_3 (m.d 2 5) (by simp) with h8128 | h8128
                                                  · linarith only [h8001, h8128, hlam]
                                                  · linarith only [h7338, h8128, hlam]
                                              · linarith only [h8125, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          rcases p8110_3 (m.d 0 2) (by simp) with h8132 | h8132
                                          · linarith only [h4, h8132, hlam]
                                          · linarith only [h0, h8132, hlam]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h4, h7337, h7338, hlam, p8006_1, p8110_2]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7338, hc02, hc23, hlam, hphi, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7337, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7993, hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h8000, hlam, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [hlam, p8110_0]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h8002, hlam, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h0, h7993, h8000, h8002, hc34, hc45, hlam, hphi, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h7993, h8000, h8002, hc34, hc45, hlam, hphi, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [h8001, hlam, p8110_1]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          rcases p8110_3 (m.d 0 2) (by simp) with h8146 | h8146
                                          · linarith only [h7338, h8146, hlam]
                                          · linarith only [h7337, h8146, hlam]
                                        · have p8110_0 := h8110c.1
                                          have p8110_1 := h8110c.2.1
                                          have p8110_2 := h8110c.2.2.1
                                          have p8110_3 := h8110c.2.2.2
                                          linarith only [hlam, p8110_0]
                                  · linarith only [h7988, h8105, hlam]
                              · linarith only [h3, h8102, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h2, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h7337, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h7987, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h7989, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h3, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h0, h7338, h7993, h8000, h8002, hc34, hc45, hlam, hphi, p8006_1]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [h7988, hlam, p8006_0]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              rcases p8006_3 (m.d 0 1) (by simp) with h8160 | h8160
                              · rcases p8006_3 (m.d 0 2) (by simp) with h8161 | h8161
                                · linarith only [h7338, h8161, hlam]
                                · linarith only [h7337, h8161, hlam]
                              · linarith only [h2, h8160, hlam]
                            · have p8006_0 := h8006c.1
                              have p8006_1 := h8006c.2.1
                              have p8006_2 := h8006c.2.2.1
                              have p8006_3 := h8006c.2.2.2
                              linarith only [hlam, p8006_0]
                      · linarith only [h4, h7988, h8001, hlam]
                    · linarith only [h0, h4, h7987, h7993, h8000, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8168 | h8168
                  · linarith only [h2, h7337, h7338, h7989, h8168, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8170 | h8170
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8171 | h8171
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8172 | h8172
                        · linarith only [h7989, h7991, h7993, h7997, h8172, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8174 | h8174
                          · linarith only [h7337, h7338, h8170, h8172, h8174, hlam]
                          · rcases h0bigk with h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c | h8176c
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              rcases p8176_3 (m.d 0 1) (by simp) with h8178 | h8178
                              · rcases p8176_3 (m.d 0 2) (by simp) with h8179 | h8179
                                · linarith only [h0, h8179, hlam]
                                · rcases p8176_3 (m.d 0 3) (by simp) with h8181 | h8181
                                  · linarith only [h1, h8181, hlam]
                                  · linarith only [h4, h8181, hlam]
                              · linarith only [h0, h8178, hlam]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7988, h7997, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p8176_1]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              rcases p8176_3 (m.d 0 1) (by simp) with h8186 | h8186
                              · rcases p8176_3 (m.d 0 2) (by simp) with h8187 | h8187
                                · linarith only [h0, h8187, hlam]
                                · linarith only [h7337, h8187, hlam]
                              · linarith only [h2, h8186, hlam]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7988, h7991, h7993, h7997, h8170, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8176_1]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h0, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h4, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7337, h7338, h8170, h8172, hc34, hc45, hlam, hphi, p8176_1]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7338, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h1, hlam, p8176_1]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              rcases p8176_3 (m.d 0 1) (by simp) with h8198 | h8198
                              · rcases p8176_3 (m.d 0 2) (by simp) with h8199 | h8199
                                · linarith only [h4, h8199, hlam]
                                · rcases p8176_3 (m.d 0 3) (by simp) with h8201 | h8201
                                  · rcases p8176_3 (m.d 0 4) (by simp) with h8202 | h8202
                                    · linarith only [h7987, h8202, hlam]
                                    · rcases p8176_3 (m.d 0 5) (by simp) with h8204 | h8204
                                      · linarith only [h7988, h8204, hlam]
                                      · linarith only [h7338, h8204, hlam]
                                  · linarith only [h4, h8201, hlam]
                              · linarith only [h0, h8198, hlam]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              rcases p8176_3 (m.d 0 1) (by simp) with h8210 | h8210
                              · rcases p8176_3 (m.d 0 2) (by simp) with h8211 | h8211
                                · linarith only [h4, h8211, hlam]
                                · linarith only [h7337, h8211, hlam]
                              · linarith only [h2, h8210, hlam]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7988, h7991, h7993, h7997, h8170, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8176_1]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h2, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7337, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7987, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7989, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h3, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h0, h7338, h7993, h8170, h8172, hc34, hc45, hlam, hphi, p8176_1]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [h7988, hlam, p8176_0]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              rcases p8176_3 (m.d 0 1) (by simp) with h8224 | h8224
                              · rcases p8176_3 (m.d 0 2) (by simp) with h8225 | h8225
                                · linarith only [h7338, h8225, hlam]
                                · linarith only [h7337, h8225, hlam]
                              · linarith only [h2, h8224, hlam]
                            · have p8176_0 := h8176c.1
                              have p8176_1 := h8176c.2.1
                              have p8176_2 := h8176c.2.2.1
                              have p8176_3 := h8176c.2.2.2
                              linarith only [hlam, p8176_0]
                      · linarith only [h4, h7988, h8171, hlam]
                    · linarith only [h4, h7988, h7991, h7993, h7997, h8170, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h7987, h7989, h7991, h7993, h7996, hc24, hc45, hlam, hphi]
          · linarith only [h7337, h7338, h7993, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h8234 | h8234
      · linarith only [h7337, h7338, h8234, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8236 | h8236
        · linarith only [h0, h4, h7337, h8236, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8238 | h8238
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8239 | h8239
            · linarith only [h0, h7338, h8239, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8241 | h8241
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8242 | h8242
                · linarith only [h1, h7988, h8242, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8244 | h8244
                  · linarith only [h2, h8234, h8244, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8246 | h8246
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8247 | h8247
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8248 | h8248
                        · linarith only [h0, h2, h4, h7988, h8234, h8238, h8247, h8248, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8250 | h8250
                          · linarith only [h4, h7337, h7988, h8246, h8247, h8248, h8250, hlam]
                          · rcases h0bigk with h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              rcases p8252_3 (m.d 0 1) (by simp) with h8254 | h8254
                              · rcases p8252_3 (m.d 0 2) (by simp) with h8255 | h8255
                                · linarith only [h0, h8255, hlam]
                                · rcases p8252_3 (m.d 0 3) (by simp) with h8257 | h8257
                                  · linarith only [h1, h8257, hlam]
                                  · linarith only [h4, h8257, hlam]
                              · linarith only [h0, h8254, hlam]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              rcases p8252_3 (m.d 0 1) (by simp) with h8261 | h8261
                              · rcases p8252_3 (m.d 0 2) (by simp) with h8262 | h8262
                                · linarith only [h0, h8262, hlam]
                                · rcases p8252_3 (m.d 0 3) (by simp) with h8264 | h8264
                                  · linarith only [h1, h8264, hlam]
                                  · rcases p8252_3 (m.d 0 4) (by simp) with h8266 | h8266
                                    · linarith only [h2, h8266, hlam]
                                    · rcases p8252_3 (m.d 0 5) (by simp) with h8268 | h8268
                                      · linarith only [h3, h8268, hlam]
                                      · linarith only [h7988, h8268, hlam]
                              · linarith only [h1, h8261, hlam]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              rcases p8252_3 (m.d 0 1) (by simp) with h8272 | h8272
                              · rcases p8252_3 (m.d 0 2) (by simp) with h8273 | h8273
                                · linarith only [h0, h8273, hlam]
                                · linarith only [h7337, h8273, hlam]
                              · linarith only [h2, h8272, hlam]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              rcases p8252_3 (m.d 0 1) (by simp) with h8277 | h8277
                              · rcases p8252_3 (m.d 0 2) (by simp) with h8278 | h8278
                                · linarith only [h0, h8278, hlam]
                                · rcases p8252_3 (m.d 0 3) (by simp) with h8280 | h8280
                                  · linarith only [h1, h8280, hlam]
                                  · rcases p8252_3 (m.d 0 4) (by simp) with h8282 | h8282
                                    · linarith only [h2, h8282, hlam]
                                    · rcases p8252_3 (m.d 0 5) (by simp) with h8284 | h8284
                                      · linarith only [h3, h8284, hlam]
                                      · rcases h2bigk with h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c | h8286c
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h4, h7988, h8238, h8246, h8247, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h4, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h4, h7988, h8246, h8247, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h7338, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h0, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8236, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h0, h4, h7988, h8246, h8247, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8239, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          rcases p8286_3 (m.d 0 2) (by simp) with h8297 | h8297
                                          · linarith only [h8297, hlam, p8286_0]
                                          · rcases p8286_3 (m.d 1 2) (by simp) with h8299 | h8299
                                            · linarith only [h8236, h8299, hlam]
                                            · rcases p8286_3 (m.d 2 3) (by simp) with h8301 | h8301
                                              · rcases p8286_3 (m.d 2 4) (by simp) with h8302 | h8302
                                                · linarith only [h8246, h8302, hlam]
                                                · rcases p8286_3 (m.d 2 5) (by simp) with h8304 | h8304
                                                  · linarith only [h8247, h8304, hlam]
                                                  · linarith only [h7338, h8304, hlam]
                                              · linarith only [h8301, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          rcases p8286_3 (m.d 0 2) (by simp) with h8308 | h8308
                                          · linarith only [h4, h8308, hlam]
                                          · linarith only [h0, h8308, hlam]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h4, h7337, h7988, h8247, hlam, p8286_2]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h4, h7988, h8247, hc02, hc23, hlam, hphi, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h7337, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8238, hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8246, hlam, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [hlam, p8286_0]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8248, hlam, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h0, h8238, h8248, hc24, hc45, hlam, hphi, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8238, h8248, hc24, hc45, hlam, hphi, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [h8247, hlam, p8286_1]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          rcases p8286_3 (m.d 0 2) (by simp) with h8322 | h8322
                                          · linarith only [h7338, h8322, hlam]
                                          · linarith only [h7337, h8322, hlam]
                                        · have p8286_0 := h8286c.1
                                          have p8286_1 := h8286c.2.1
                                          have p8286_2 := h8286c.2.2.1
                                          have p8286_3 := h8286c.2.2.2
                                          linarith only [hlam, p8286_0]
                              · linarith only [h3, h8277, hlam]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h0, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h4, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h7337, h7338, h8246, h8248, hc34, hc45, hlam, hphi, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h7338, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h1, hlam, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h7988, hc02, hc35, hlam, hphi, ht23, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h2, h7988, h8238, h8246, h8247, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h7988, hlam, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h2, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h7337, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h7987, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h8234, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h3, hlam, p8252_0]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h0, h7338, h8238, h8246, h8248, hc34, hc45, hlam, hphi, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [h0, h4, h7988, h8238, h8246, h8247, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8252_1]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              rcases p8252_3 (m.d 0 1) (by simp) with h8345 | h8345
                              · rcases p8252_3 (m.d 0 2) (by simp) with h8346 | h8346
                                · linarith only [h7338, h8346, hlam]
                                · linarith only [h7337, h8346, hlam]
                              · linarith only [h2, h8345, hlam]
                            · have p8252_0 := h8252c.1
                              have p8252_1 := h8252c.2.1
                              have p8252_2 := h8252c.2.2.1
                              have p8252_3 := h8252c.2.2.2
                              linarith only [hlam, p8252_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8351 | h8351
                        · linarith only [h0, h4, h8234, h8238, h8247, h8351, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8353 | h8353
                          · linarith only [h0, h4, h8238, h8246, h8247, h8351, h8353, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h4, h8238, h8246, h8247, h8353, hc34, hc45, hlam, hphi]
                    · linarith only [h0, h4, h7987, h8238, h8246, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h7987, h7988, h8241, hc13, hc35, hlam, hphi]
          · linarith only [h4, h7337, h8238, hc12, hc23, hlam, hphi]
  · linarith only [h4, h7337, h7987, hlam]

set_option maxHeartbeats 11162000 in
set_option maxHeartbeats 11162000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s10_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7337 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h7338 | h7338
  · exact r1l7_10_12_23_L_I_L_I_H_I_s10_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h7337 h7338
  · exact r1l7_10_12_23_L_I_L_I_H_I_s10_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h7337 h7338

set_option maxHeartbeats 11162000 in
set_option maxHeartbeats 11162000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s10_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  exact r1l7_10_12_23_L_I_L_I_H_I_s11 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h7337

set_option maxHeartbeats 11162000 in
set_option maxHeartbeats 11162000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s10 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h7337 | h7337
  · exact r1l7_10_12_23_L_I_L_I_H_I_s10_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h7337
  · exact r1l7_10_12_23_L_I_L_I_H_I_s10_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h7337

set_option maxHeartbeats 25828000 in
set_option maxHeartbeats 25828000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_23_L_I_L_I_H_I_s4 m hb0 hb2 hb3 h0 h1 h2 h3 h4
  · exact r1l7_10_12_23_L_I_L_I_H_I_s10 m hb0 hb2 hb3 h0 h1 h2 h3 h4

set_option maxHeartbeats 26076000 in
set_option maxHeartbeats 26076000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_23_L_I_L_I_H_I_s3 m hb0 hb2 hb3 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h12918 | h12918
    · rcases m.htr 0 2 4 (by decide) (by decide) with h12919 | h12919
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12920 | h12920
        · linarith only [h0, h12920, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12922 | h12922
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12923 | h12923
            · linarith only [h1, h12923, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12925 | h12925
              · linarith only [h12925, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12927 | h12927
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12928 | h12928
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12929 | h12929
                    · linarith only [h0, h12920, h12929, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h12931 | h12931
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12932 | h12932
                        · linarith only [h0, h12922, h12923, h12927, h12929, h12932, h2, h3, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h12927, h12932, h3, hc23, hc35, hlam, hphi]
                      · linarith only [h12922, h12923, h12931, hc13, hc35, hlam, hphi]
                  · linarith only [h12919, h12920, h12928, hc12, hc25, hlam, hphi]
                · linarith only [h12918, h12920, h12927, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12938 | h12938
            · linarith only [h1, h12938, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12940 | h12940
              · linarith only [h0, h12919, h12940, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12942 | h12942
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12943 | h12943
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12944 | h12944
                    · linarith only [h0, h12920, h12944, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h12946 | h12946
                      · linarith only [h1, h12922, h12946, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12948 | h12948
                        · linarith only [h1, h12938, h12948, hlam]
                        · linarith only [h0, h12942, h12948, h3, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h12919, h12942, h12943, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h12918, h12920, h12942, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12953 | h12953
        · linarith only [h12919, h12953, h2, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12955 | h12955
          · linarith only [h12918, h12919, h12955, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12957 | h12957
            · linarith only [h0, h12918, h12957, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12959 | h12959
              · linarith only [h12959, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12961 | h12961
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12962 | h12962
                  · linarith only [h0, h12919, h12962, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12964 | h12964
                    · linarith only [h0, h12953, h12964, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h12966 | h12966
                      · linarith only [h1, h12955, h12964, h12966, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12968 | h12968
                        · linarith only [h1, h12957, h12968, hlam]
                        · linarith only [h12961, h12962, h12968, h2, h3, hc23, hc35, hlam, hphi]
                · linarith only [h12918, h12919, h12961, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h12972 | h12972
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12973 | h12973
        · linarith only [h1, h12918, h12973, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12975 | h12975
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12976 | h12976
            · linarith only [h1, h12976, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12978 | h12978
              · linarith only [h1, h12918, h12972, h12978, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12980 | h12980
                · linarith only [h0, h12918, h12980, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12982 | h12982
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12983 | h12983
                    · linarith only [h0, h12973, h12983, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h12985 | h12985
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12986 | h12986
                        · linarith only [h1, h12918, h12976, h12983, h12986, h3, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12988 | h12988
                          · linarith only [h1, h12978, h12980, h12982, h12988, h3, hlam]
                          · linarith only [h1, h12980, h12982, h12988, h3, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h12975, h12980, h12982, h12985, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h12918, h12972, h12976, h12982, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h12918, h12972, h12975, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12994 | h12994
        · linarith only [h0, h12994, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12996 | h12996
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12997 | h12997
            · linarith only [h1, h12997, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12999 | h12999
              · linarith only [h1, h12996, h12999, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13001 | h13001
                · linarith only [h0, h12918, h13001, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13003 | h13003
                  · linarith only [h0, h12972, h13003, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13005 | h13005
                    · linarith only [h1, h12994, h13001, h13005, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13007 | h13007
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13008 | h13008
                        · linarith only [h1, h12997, h13005, h13008, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13010 | h13010
                          · linarith only [h1, h12999, h13007, h13010, h3, hlam]
                          · linarith only [h1, h13007, h13010, h3, hc34, hc45, hlam, hphi]
                      · linarith only [h12996, h12997, h13007, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13014 | h13014
            · linarith only [h12996, h13014, h2, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13016 | h13016
              · linarith only [h13016, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13018 | h13018
                · linarith only [h0, h12918, h13018, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13020 | h13020
                  · linarith only [h1, h12972, h12996, h13018, h13020, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13022 | h13022
                    · linarith only [h0, h12994, h13022, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13024 | h13024
                      · linarith only [h1, h12996, h13024, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13026 | h13026
                        · linarith only [h1, h13014, h13026, h3, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13028 | h13028
                          · linarith only [h13016, h13028, h2, h3, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13030 | h13030
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13031 | h13031
                              · linarith only [h0, h13026, h13031, h3, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h12918, h12996, h13030, h13031, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13034 | h13034
                              · linarith only [h0, h12918, h13014, h13030, h13034, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13036 | h13036
                                · linarith only [h13018, h13024, h13028, h13036, h2, h3, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13038 | h13038
                                  · linarith only [h0, h12918, h13030, h13036, h13038, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h12918, h13030, h13038, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 26724000 in
set_option maxHeartbeats 26724000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_I_L_I_H_I_s2 m hb0 hb2 hb3 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h13041 | h13041
    · rcases m.htr 0 2 3 (by decide) (by decide) with h13042 | h13042
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13043 | h13043
        · linarith only [h0, h13043, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13045 | h13045
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13046 | h13046
            · linarith only [h1, h13046, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13048 | h13048
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13049 | h13049
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13050 | h13050
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13051 | h13051
                    · linarith only [h0, h13043, h13051, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13053 | h13053
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13054 | h13054
                        · linarith only [h1, h13046, h13054, h2, hlam]
                        · linarith only [h0, h13050, h13054, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h13045, h13050, h13053, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h13042, h13043, h13050, hc12, hc24, hlam, hphi]
                · linarith only [h1, h13048, h13049, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13060 | h13060
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13061 | h13061
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13062 | h13062
                    · linarith only [h0, h13043, h13062, h2, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13064 | h13064
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13065 | h13065
                        · linarith only [h1, h13046, h13065, hlam]
                        · linarith only [h0, h13061, h13065, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h13045, h13061, h13062, h13064, h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h13042, h13043, h13061, hc12, hc24, hlam, hphi]
                · linarith only [h0, h13045, h13060, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13071 | h13071
            · linarith only [h1, h13071, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13073 | h13073
              · linarith only [h13042, h13045, h13073, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13075 | h13075
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13076 | h13076
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13077 | h13077
                    · linarith only [h0, h13043, h13077, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13079 | h13079
                      · linarith only [h0, h13045, h13079, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13081 | h13081
                        · linarith only [h1, h13071, h13081, h2, hlam]
                        · linarith only [h0, h13076, h13081, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h13042, h13043, h13076, hc12, hc24, hlam, hphi]
                · linarith only [h13041, h13075, h2, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13086 | h13086
        · linarith only [h0, h13086, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13088 | h13088
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13089 | h13089
            · linarith only [h1, h13089, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13091 | h13091
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13092 | h13092
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13093 | h13093
                  · linarith only [h0, h13042, h13088, h13093, h2, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13095 | h13095
                    · linarith only [h0, h13086, h13095, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13097 | h13097
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13098 | h13098
                        · linarith only [h1, h13089, h13098, h2, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13100 | h13100
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13101 | h13101
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13102 | h13102
                              · linarith only [h1, h13098, h13100, h13102, h2, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13104 | h13104
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13105 | h13105
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13106 | h13106
                                    · rcases h0bigk with h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c | h13107c
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h0, h13097, h13104, h13106, h2, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h0, h13042, h13097, h13104, h13106, h2, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h2, hlam, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        rcases p13107_3 (m.d 0 1) (by simp) with h13112 | h13112
                                        · rcases p13107_3 (m.d 0 2) (by simp) with h13113 | h13113
                                          · linarith only [h0, h13113, hlam]
                                          · linarith only [h13088, h13113, hlam]
                                        · linarith only [h13041, h13112, hlam]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h0, hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13042, hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13086, hlam, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13041, h13042, h13102, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h1, hlam, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h1, h13095, h13102, h2, hc02, hc34, hlam, hphi, ht23, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13089, hlam, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        rcases p13107_3 (m.d 0 1) (by simp) with h13126 | h13126
                                        · rcases p13107_3 (m.d 0 2) (by simp) with h13127 | h13127
                                          · linarith only [h13042, h13127, hlam]
                                          · linarith only [h13088, h13127, hlam]
                                        · linarith only [h13041, h13126, hlam]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h0, h13097, h13104, h13106, hc04, hc45, hlam, hphi, ht0b, ht5b, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        rcases p13107_3 (m.d 0 1) (by simp) with h13132 | h13132
                                        · linarith only [h13132, h2, hlam]
                                        · linarith only [h0, h13132, hlam]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        rcases p13107_3 (m.d 0 1) (by simp) with h13135 | h13135
                                        · linarith only [h13135, h2, hlam]
                                        · linarith only [h1, h13135, hlam]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        rcases p13107_3 (m.d 0 1) (by simp) with h13139 | h13139
                                        · linarith only [h13139, h2, hlam]
                                        · linarith only [h13041, h13139, hlam]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13041, hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13088, hlam, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13091, hlam, p13107_0]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [h13092, hlam, p13107_1]
                                      · have p13107_0 := h13107c.1
                                        have p13107_1 := h13107c.2.1
                                        have p13107_2 := h13107c.2.2.1
                                        have p13107_3 := h13107c.2.2.2
                                        linarith only [hlam, p13107_0]
                                    · linarith only [h1, h13093, h13095, h13102, h13106, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h13041, h13093, h13095, h13097, h13101, h13104, h13105, h2, hc05, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h13042, h13091, h13097, h13104, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h13093, h13097, h13101, h2, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h13091, h13093, h13097, h13100, h2, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h13088, h13095, h13097, h2, hc12, hc24, hlam, hphi]
                · linarith only [h1, h13042, h13088, h13092, h2, hlam]
              · linarith only [h13042, h13088, h13091, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13155 | h13155
            · linarith only [h1, h13155, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13157 | h13157
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13158 | h13158
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13159 | h13159
                  · linarith only [h0, h13042, h13159, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13161 | h13161
                    · linarith only [h0, h13086, h13161, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13163 | h13163
                      · linarith only [h0, h13088, h13163, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13165 | h13165
                        · linarith only [h1, h13155, h13161, h13165, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13167 | h13167
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13168 | h13168
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13169 | h13169
                              · linarith only [h0, h13165, h13169, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13171 | h13171
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13172 | h13172
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13173 | h13173
                                    · rcases h0bigk with h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c | h13174c
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h0, h13161, h2, hc12, hc24, hlam, hphi, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h1, h13161, h13167, h13169, h13173, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h2, hlam, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h0, h13088, h13161, h13169, h2, hc12, hc34, hlam, hphi, ht23, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h0, hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13042, hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13086, hlam, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13088, hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h1, hlam, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h0, h1, h13161, h13169, h2, hc12, hc34, hlam, hphi, ht23, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13155, hlam, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h0, h1, h13088, h13161, h13169, h2, hc12, hc34, hlam, hphi, ht23, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h1, h13167, h13173, hc04, hc45, hlam, hphi, ht0b, ht5b, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        rcases p13174_3 (m.d 0 1) (by simp) with h13191 | h13191
                                        · linarith only [h13191, h2, hlam]
                                        · linarith only [h0, h13191, hlam]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        rcases p13174_3 (m.d 0 1) (by simp) with h13194 | h13194
                                        · linarith only [h13194, h2, hlam]
                                        · linarith only [h1, h13194, hlam]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        rcases p13174_3 (m.d 0 1) (by simp) with h13198 | h13198
                                        · linarith only [h13198, h2, hlam]
                                        · linarith only [h13041, h13198, hlam]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13041, hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h0, h13041, h13161, h13169, h2, hc12, hc34, hlam, hphi, ht23, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13157, hlam, p13174_0]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [h13158, hlam, p13174_1]
                                      · have p13174_0 := h13174c.1
                                        have p13174_1 := h13174c.2.1
                                        have p13174_2 := h13174c.2.2.1
                                        have p13174_3 := h13174c.2.2.2
                                        linarith only [hlam, p13174_0]
                                    · linarith only [h0, h13161, h13169, h13173, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h13161, h13167, h13168, h13172, h2, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1, h13167, h13171, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h13157, h13158, h13167, h13168, h2, hc03, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h13157, h13159, h13165, h13167, h2, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h13157, h13158, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13212 | h13212
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13213 | h13213
                  · linarith only [h0, h13042, h13213, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13215 | h13215
                    · linarith only [h0, h13086, h13215, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13217 | h13217
                      · linarith only [h0, h13088, h13217, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13219 | h13219
                        · linarith only [h1, h13155, h13215, h13219, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13221 | h13221
                          · linarith only [h1, h13157, h13221, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13223 | h13223
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13224 | h13224
                              · linarith only [h0, h13219, h13224, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13226 | h13226
                                · linarith only [h13157, h13224, h13226, hc03, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13228 | h13228
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13229 | h13229
                                    · rcases h0bigk with h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c | h13230c
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h0, h13215, h13224, h2, hc12, hc34, hlam, hphi, ht23, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h1, h13213, h13215, h13224, h2, hc12, hc34, hlam, hphi, ht23, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h2, hlam, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13041, h13213, h13215, h13221, h13224, h2, hc12, hc34, hlam, hphi, ht23, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h0, hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13042, hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13086, hlam, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13088, hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h1, hlam, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h0, h13042, h13226, h13229, hc12, hc34, hlam, hphi, ht23, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13155, hlam, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13157, hlam, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h1, h13086, h13224, hc13, hc34, hlam, hphi, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        rcases p13230_3 (m.d 0 1) (by simp) with h13247 | h13247
                                        · linarith only [h13247, h2, hlam]
                                        · linarith only [h0, h13247, hlam]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        rcases p13230_3 (m.d 0 1) (by simp) with h13250 | h13250
                                        · linarith only [h13250, h2, hlam]
                                        · linarith only [h1, h13250, hlam]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        rcases p13230_3 (m.d 0 1) (by simp) with h13254 | h13254
                                        · linarith only [h13254, h2, hlam]
                                        · linarith only [h13041, h13254, hlam]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13041, hlam, p13230_0]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h0, h13041, h13215, h13224, h2, hc12, hc34, hlam, hphi, ht23, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h1, h13041, h13213, h13215, h13224, h2, hc12, hc34, hlam, hphi, ht23, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [h13212, hlam, p13230_1]
                                      · have p13230_0 := h13230c.1
                                        have p13230_1 := h13230c.2.1
                                        have p13230_2 := h13230c.2.2.1
                                        have p13230_3 := h13230c.2.2.2
                                        linarith only [hlam, p13230_0]
                                    · linarith only [h0, h13215, h13224, h13229, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h13041, h13215, h13223, h13228, h2, hlam]
                            · linarith only [h13041, h13213, h13221, h13223, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h13041, h13212, h2, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h13266 | h13266
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13267 | h13267
        · linarith only [h0, h13267, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13269 | h13269
          · linarith only [h0, h13041, h13269, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13271 | h13271
            · linarith only [h1, h13271, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13273 | h13273
              · linarith only [h0, h13041, h13266, h13273, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13275 | h13275
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13276 | h13276
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13277 | h13277
                    · linarith only [h0, h13267, h13277, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13279 | h13279
                      · linarith only [h0, h13041, h13269, h13279, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13281 | h13281
                        · linarith only [h1, h13271, h13277, h13281, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h13276, h13281, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h13266, h13267, h13276, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13285 | h13285
                  · linarith only [h0, h13275, h13285, h2, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h13266, h13275, h13285, h2, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13288 | h13288
        · linarith only [h1, h13266, h13288, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13290 | h13290
          · linarith only [h1, h13041, h13266, h13290, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13292 | h13292
            · linarith only [h1, h13292, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13294 | h13294
              · linarith only [h1, h13041, h13294, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13296 | h13296
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13297 | h13297
                  · linarith only [h0, h13266, h13297, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13299 | h13299
                    · linarith only [h0, h13041, h13288, h13296, h13299, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13301 | h13301
                      · linarith only [h1, h13041, h13290, h13297, h13301, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13303 | h13303
                        · linarith only [h1, h13292, h13299, h13303, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13305 | h13305
                          · linarith only [h1, h13041, h13294, h13305, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13307 | h13307
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13308 | h13308
                              · linarith only [h1, h13041, h13297, h13303, h13307, h13308, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13310 | h13310
                                · linarith only [h1, h13041, h13297, h13305, h13310, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13312 | h13312
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13313 | h13313
                                    · rcases h0bigk with h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c | h13314c
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13041, h13299, h13307, hc02, hc24, hlam, hphi, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h1, h13041, h13297, h13299, h13307, hc12, hc24, hlam, hphi, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h2, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13041, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h0, hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13266, hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13288, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13290, hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h1, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h0, h1, h13041, h13299, h13307, hc12, hc24, hlam, hphi, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13292, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13294, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h0, h13299, h2, hc12, hc24, hlam, hphi, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        rcases p13314_3 (m.d 0 1) (by simp) with h13331 | h13331
                                        · linarith only [h13331, h2, hlam]
                                        · linarith only [h0, h13331, hlam]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        rcases p13314_3 (m.d 0 1) (by simp) with h13334 | h13334
                                        · linarith only [h13334, h2, hlam]
                                        · linarith only [h1, h13334, hlam]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [hlam, p13314_0]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h1, h13041, h13297, h13299, h13308, h2, hc12, hc34, hlam, hphi, ht23, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h1, h13041, h13297, h13299, h13307, h13308, hc12, hc34, hlam, hphi, ht23, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        rcases p13314_3 (m.d 0 1) (by simp) with h13340 | h13340
                                        · linarith only [h13041, h13340, hlam]
                                        · linarith only [h0, h13340, hlam]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        rcases p13314_3 (m.d 0 1) (by simp) with h13343 | h13343
                                        · linarith only [h13041, h13343, hlam]
                                        · linarith only [h1, h13343, hlam]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [h13296, hlam, p13314_1]
                                      · have p13314_0 := h13314c.1
                                        have p13314_1 := h13314c.2.1
                                        have p13314_2 := h13314c.2.2.1
                                        have p13314_3 := h13314c.2.2.2
                                        linarith only [hlam, p13314_0]
                                    · linarith only [h13296, h13299, h13308, h13313, h2, hlam]
                                  · linarith only [h13296, h13299, h13312, h2, hlam]
                            · linarith only [h13296, h13307, h2, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13351 | h13351
                  · linarith only [h0, h13296, h13351, h2, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13353 | h13353
                    · linarith only [h1, h13296, h13351, h13353, h2, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13355 | h13355
                      · linarith only [h0, h13290, h13355, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13357 | h13357
                        · linarith only [h1, h13296, h13357, h2, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13359 | h13359
                          · linarith only [h1, h13266, h13294, h13296, h13359, h2, hc02, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13361 | h13361
                            · linarith only [h1, h13296, h13357, h13361, h2, hc13, hc34, hlam, hphi]
                            · linarith only [h1, h13351, h13361, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 28790000 in
set_option maxHeartbeats 28790000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  exact r1l7_10_12_23_L_I_L_I_H_I_s1 m hb0 hb2 hb3 h0 h1

end R2N4
