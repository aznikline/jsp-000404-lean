import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8676 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8677 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8678 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h9064 | h9064
  · linarith only [h0, h4, h8674, h9064, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h9066 | h9066
    · rcases m.htr 1 2 5 (by decide) (by decide) with h9067 | h9067
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9068 | h9068
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9069 | h9069
          · rcases m.htr 1 4 5 (by decide) (by decide) with h9070 | h9070
            · linarith only [h2, h8678, h9070, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9072 | h9072
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9073 | h9073
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9074 | h9074
                  · linarith only [h2, h8678, h9066, h9074, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9076 | h9076
                    · linarith only [h2, h8678, h9066, h9072, h9076, hlam]
                    · rcases h1bigk with h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9080 | h9080
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9081 | h9081
                          · linarith only [h9081, hlam, p9078_0]
                          · rcases p9078_3 (m.d 1 3) (by simp) with h9083 | h9083
                            · linarith only [h1, h9083, hlam]
                            · linarith only [h9064, h9083, hlam]
                        · linarith only [h9080, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9087 | h9087
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9088 | h9088
                          · linarith only [h0, h9088, hlam]
                          · rcases p9078_3 (m.d 1 3) (by simp) with h9090 | h9090
                            · linarith only [h9090, hlam, p9078_0]
                            · rcases p9078_3 (m.d 1 4) (by simp) with h9092 | h9092
                              · linarith only [h2, h9092, hlam]
                              · rcases p9078_3 (m.d 1 5) (by simp) with h9094 | h9094
                                · linarith only [h3, h9094, hlam]
                                · rcases h3bigk with h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c | h9096c
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9098 | h9098
                                    · rcases p9096_3 (m.d 1 3) (by simp) with h9099 | h9099
                                      · linarith only [h1, h9099, hlam]
                                      · rcases p9096_3 (m.d 2 3) (by simp) with h9101 | h9101
                                        · rcases p9096_3 (m.d 3 4) (by simp) with h9102 | h9102
                                          · linarith only [h8676, h9102, hlam]
                                          · rcases p9096_3 (m.d 3 5) (by simp) with h9104 | h9104
                                            · linarith only [h8677, h9104, hlam]
                                            · rcases h5bigk with h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c | h9106c
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h4, h8675, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h4, h8675, h9072, h9074, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h4, h8675, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h8678, hlam, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h3, hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h3, h9072, h9074, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9070, hlam, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h8675, hlam, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9067, hlam, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h4, h8675, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9074, hlam, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h8677, hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9069, hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9073, hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [hlam, p9106_0]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9076, hlam, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h2, h8678, h9066, h9072, hc34, hc45, hlam, hphi, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9066, h9070, h9072, hc34, hc45, hlam, hphi, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9072, h9074, hc34, hc45, hlam, hphi, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [h9076, hc34, hc45, hlam, hphi, p9106_1]
                                              · have p9106_0 := h9106c.1
                                                have p9106_1 := h9106c.2.1
                                                have p9106_2 := h9106c.2.2.1
                                                have p9106_3 := h9106c.2.2.2
                                                linarith only [hlam, p9106_0]
                                        · linarith only [h9064, h9101, hlam]
                                    · linarith only [h1, h9098, hlam]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h4, hlam, p9096_1]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9135 | h9135
                                    · rcases p9096_3 (m.d 1 3) (by simp) with h9136 | h9136
                                      · linarith only [h1, h9136, hlam]
                                      · linarith only [h9068, h9136, hlam]
                                    · linarith only [h9135, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9140 | h9140
                                    · rcases p9096_3 (m.d 1 3) (by simp) with h9141 | h9141
                                      · linarith only [h1, h9141, hlam]
                                      · linarith only [h9069, h9141, hlam]
                                    · linarith only [h9140, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h1, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9064, hlam, p9096_1]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9078_1, p9096_1]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9076, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9078_1, p9096_1]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9150 | h9150
                                    · linarith only [h4, h9150, hlam]
                                    · rcases p9096_3 (m.d 1 3) (by simp) with h9152 | h9152
                                      · linarith only [h9064, h9152, hlam]
                                      · rcases p9096_3 (m.d 2 3) (by simp) with h9154 | h9154
                                        · rcases p9096_3 (m.d 3 4) (by simp) with h9155 | h9155
                                          · linarith only [h9072, h9155, hlam]
                                          · rcases p9096_3 (m.d 3 5) (by simp) with h9157 | h9157
                                            · linarith only [h9073, h9157, hlam]
                                            · rcases h5bigk with h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c | h9159c
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h4, h8675, h9066, h9070, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9096_1, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h4, h8675, h9072, h9074, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9096_1, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h4, h8675, h9076, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9096_1, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h8678, hlam, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h3, hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h3, h9072, h9074, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h0, h9067, h9076, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9070, hlam, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h8675, hlam, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9067, hlam, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h4, h8675, h9076, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9096_1, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9074, hlam, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h8677, hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9069, hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9073, hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [hlam, p9159_0]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9076, hlam, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h8677, h9076, hc34, hc45, hlam, hphi, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9069, h9076, hc34, hc45, hlam, hphi, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9073, h9076, hc34, hc45, hlam, hphi, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [h9076, hc34, hc45, hlam, hphi, p9159_1]
                                              · have p9159_0 := h9159c.1
                                                have p9159_1 := h9159c.2.1
                                                have p9159_2 := h9159c.2.2.1
                                                have p9159_3 := h9159c.2.2.2
                                                linarith only [hlam, p9159_0]
                                        · linarith only [h4, h9154, hlam]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9186 | h9186
                                    · linarith only [h4, h9186, hlam]
                                    · linarith only [h1, h9186, hlam]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9190 | h9190
                                    · linarith only [h4, h9190, hlam]
                                    · linarith only [h8676, h9190, hlam]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    rcases p9096_3 (m.d 0 3) (by simp) with h9193 | h9193
                                    · linarith only [h4, h9193, hlam]
                                    · linarith only [h8677, h9193, hlam]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h8676, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9068, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9072, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9076, hlam, p9096_1]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h8677, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9069, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h9073, hlam, p9096_0]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [h0, h9067, h9073, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9096_1]
                                  · have p9096_0 := h9096c.1
                                    have p9096_1 := h9096c.2.1
                                    have p9096_2 := h9096c.2.2.1
                                    have p9096_3 := h9096c.2.2.2
                                    linarith only [hlam, p9096_0]
                        · linarith only [h9087, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9207 | h9207
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9208 | h9208
                          · linarith only [h0, h9208, hlam]
                          · linarith only [h9066, h9208, hlam]
                        · linarith only [h9207, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9212 | h9212
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9213 | h9213
                          · linarith only [h0, h9213, hlam]
                          · linarith only [h9067, h9213, hlam]
                        · linarith only [h9212, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h0, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h9064, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9220 | h9220
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9221 | h9221
                          · rcases p9078_3 (m.d 1 3) (by simp) with h9222 | h9222
                            · rcases p9078_3 (m.d 1 4) (by simp) with h9223 | h9223
                              · linarith only [h9066, h9223, hlam]
                              · rcases p9078_3 (m.d 1 5) (by simp) with h9225 | h9225
                                · linarith only [h9067, h9225, hlam]
                                · linarith only [h9070, h9225, hlam]
                            · linarith only [h9068, h9222, hlam]
                          · linarith only [h9066, h9221, hlam]
                        · linarith only [h2, h9220, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9231 | h9231
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9232 | h9232
                          · rcases p9078_3 (m.d 1 3) (by simp) with h9233 | h9233
                            · rcases p9078_3 (m.d 1 4) (by simp) with h9234 | h9234
                              · linarith only [h9066, h9234, hlam]
                              · rcases p9078_3 (m.d 1 5) (by simp) with h9236 | h9236
                                · linarith only [h9067, h9236, hlam]
                                · rcases h3bigk with h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c | h9238c
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9064, h9070, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p9078_1, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h4, hlam, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    rcases p9238_3 (m.d 0 3) (by simp) with h9242 | h9242
                                    · rcases p9238_3 (m.d 1 3) (by simp) with h9243 | h9243
                                      · linarith only [h1, h9243, hlam]
                                      · linarith only [h9068, h9243, hlam]
                                    · linarith only [h9242, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    rcases p9238_3 (m.d 0 3) (by simp) with h9247 | h9247
                                    · rcases p9238_3 (m.d 1 3) (by simp) with h9248 | h9248
                                      · linarith only [h1, h9248, hlam]
                                      · linarith only [h9069, h9248, hlam]
                                    · linarith only [h9247, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h1, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9064, hlam, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    rcases p9238_3 (m.d 0 3) (by simp) with h9255 | h9255
                                    · rcases p9238_3 (m.d 1 3) (by simp) with h9256 | h9256
                                      · rcases p9238_3 (m.d 2 3) (by simp) with h9257 | h9257
                                        · rcases p9238_3 (m.d 3 4) (by simp) with h9258 | h9258
                                          · linarith only [h9258, hlam, p9238_0]
                                          · rcases p9238_3 (m.d 3 5) (by simp) with h9260 | h9260
                                            · linarith only [h9069, h9260, hlam]
                                            · linarith only [h9076, h9260, hlam]
                                        · linarith only [h9072, h9257, hlam]
                                      · linarith only [h9256, hlam, p9238_0]
                                    · linarith only [h8676, h9255, hlam]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    rcases p9238_3 (m.d 0 3) (by simp) with h9266 | h9266
                                    · rcases p9238_3 (m.d 1 3) (by simp) with h9267 | h9267
                                      · rcases p9238_3 (m.d 2 3) (by simp) with h9268 | h9268
                                        · rcases p9238_3 (m.d 3 4) (by simp) with h9269 | h9269
                                          · linarith only [h9068, h9269, hlam]
                                          · rcases p9238_3 (m.d 3 5) (by simp) with h9271 | h9271
                                            · linarith only [h9271, hlam, p9238_0]
                                            · rcases h5bigk with h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c | h9273c
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h4, h8675, h9066, h9070, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h4, h8675, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h4, h8675, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h8678, hlam, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h3, hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9073, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p9078_1, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h0, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9078_1, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9070, hlam, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h8675, hlam, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9067, hlam, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h4, h8675, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9074, hlam, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h8677, hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9069, hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9073, hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [hlam, p9273_0]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9076, hlam, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h2, h8678, h9066, h9072, hc34, hc45, hlam, hphi, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9066, h9070, h9072, hc34, hc45, hlam, hphi, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9072, h9074, hc34, hc45, hlam, hphi, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [h9076, hc34, hc45, hlam, hphi, p9273_1]
                                              · have p9273_0 := h9273c.1
                                                have p9273_1 := h9273c.2.1
                                                have p9273_2 := h9273c.2.2.1
                                                have p9273_3 := h9273c.2.2.2
                                                linarith only [hlam, p9273_0]
                                        · linarith only [h9073, h9268, hlam]
                                      · linarith only [h9267, hlam, p9238_0]
                                    · linarith only [h8677, h9266, hlam]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h0, h4, h9066, h9070, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9078_1, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9064, h9066, h9070, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9078_1, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h0, h4, h9066, h9070, h9072, hlam, p9078_1, p9238_2]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h0, h4, h9069, hlam, p9078_1, p9238_2]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h8676, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9068, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9072, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9076, hlam, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h8677, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9069, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h9073, hlam, p9238_0]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [h4, h8675, h9073, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9238_1]
                                  · have p9238_0 := h9238c.1
                                    have p9238_1 := h9238c.2.1
                                    have p9238_2 := h9238c.2.2.1
                                    have p9238_3 := h9238c.2.2.2
                                    linarith only [hlam, p9238_0]
                            · linarith only [h9069, h9233, hlam]
                          · linarith only [h9067, h9232, hlam]
                        · linarith only [h3, h9231, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h1, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h1, h9066, h9072, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9323 | h9323
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9324 | h9324
                          · linarith only [h9064, h9324, hlam]
                          · linarith only [h9066, h9324, hlam]
                        · linarith only [h2, h9323, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9328 | h9328
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9329 | h9329
                          · linarith only [h9064, h9329, hlam]
                          · linarith only [h9067, h9329, hlam]
                        · linarith only [h3, h9328, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h2, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h9066, hlam, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h9068, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h9070, hlam, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h3, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h9067, hlam, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h9069, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 1) (by simp) with h9341 | h9341
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9342 | h9342
                          · rcases p9078_3 (m.d 1 3) (by simp) with h9343 | h9343
                            · rcases p9078_3 (m.d 1 4) (by simp) with h9344 | h9344
                              · linarith only [h9070, h9344, hlam]
                              · rcases p9078_3 (m.d 1 5) (by simp) with h9346 | h9346
                                · rcases h3bigk with h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c | h9347c
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h4, h9064, h9066, h9067, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9078_1, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h4, hlam, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    rcases p9347_3 (m.d 0 3) (by simp) with h9351 | h9351
                                    · rcases p9347_3 (m.d 1 3) (by simp) with h9352 | h9352
                                      · linarith only [h1, h9352, hlam]
                                      · linarith only [h9068, h9352, hlam]
                                    · linarith only [h9351, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    rcases p9347_3 (m.d 0 3) (by simp) with h9356 | h9356
                                    · rcases p9347_3 (m.d 1 3) (by simp) with h9357 | h9357
                                      · linarith only [h1, h9357, hlam]
                                      · linarith only [h9069, h9357, hlam]
                                    · linarith only [h9356, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h1, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9064, hlam, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    rcases p9347_3 (m.d 0 3) (by simp) with h9364 | h9364
                                    · rcases p9347_3 (m.d 1 3) (by simp) with h9365 | h9365
                                      · rcases p9347_3 (m.d 2 3) (by simp) with h9366 | h9366
                                        · rcases p9347_3 (m.d 3 4) (by simp) with h9367 | h9367
                                          · linarith only [h9367, hlam, p9347_0]
                                          · rcases p9347_3 (m.d 3 5) (by simp) with h9369 | h9369
                                            · linarith only [h9069, h9369, hlam]
                                            · linarith only [h9076, h9369, hlam]
                                        · linarith only [h9072, h9366, hlam]
                                      · linarith only [h9365, hlam, p9347_0]
                                    · linarith only [h8676, h9364, hlam]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    rcases p9347_3 (m.d 0 3) (by simp) with h9375 | h9375
                                    · rcases p9347_3 (m.d 1 3) (by simp) with h9376 | h9376
                                      · rcases p9347_3 (m.d 2 3) (by simp) with h9377 | h9377
                                        · rcases p9347_3 (m.d 3 4) (by simp) with h9378 | h9378
                                          · linarith only [h9068, h9378, hlam]
                                          · rcases p9347_3 (m.d 3 5) (by simp) with h9380 | h9380
                                            · linarith only [h9380, hlam, p9347_0]
                                            · rcases h5bigk with h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9066, h9072, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p9078_1, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h4, h8675, h9072, h9074, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h4, h8675, h9076, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h8678, hlam, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h3, hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h0, h9067, h9072, h9074, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h0, h4, h9067, h9076, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9070, hlam, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h8675, hlam, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9067, hlam, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h4, h8675, h9076, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9074, hlam, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h8677, hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9069, hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9073, hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [hlam, p9382_0]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9076, hlam, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h8677, h9076, hc34, hc45, hlam, hphi, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9069, h9076, hc34, hc45, hlam, hphi, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9073, h9076, hc34, hc45, hlam, hphi, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [h9076, hc34, hc45, hlam, hphi, p9382_1]
                                              · have p9382_0 := h9382c.1
                                                have p9382_1 := h9382c.2.1
                                                have p9382_2 := h9382c.2.2.1
                                                have p9382_3 := h9382c.2.2.2
                                                linarith only [hlam, p9382_0]
                                        · linarith only [h9073, h9377, hlam]
                                      · linarith only [h9376, hlam, p9347_0]
                                    · linarith only [h8677, h9375, hlam]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h3, h4, h8675, h9066, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9078_1, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9064, h9066, h9067, h9072, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9078_1, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h3, h4, h8675, h9066, h9072, hlam, p9078_1, p9347_2]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    rcases p9347_3 (m.d 0 3) (by simp) with h9415 | h9415
                                    · linarith only [h4, h9415, hlam]
                                    · linarith only [h8677, h9415, hlam]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h8676, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9068, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9072, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9076, hlam, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h8677, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9069, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h9073, hlam, p9347_0]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [h4, h8675, h9073, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9347_1]
                                  · have p9347_0 := h9347c.1
                                    have p9347_1 := h9347c.2.1
                                    have p9347_2 := h9347c.2.2.1
                                    have p9347_3 := h9347c.2.2.2
                                    linarith only [hlam, p9347_0]
                                · linarith only [h9070, h9346, hlam]
                            · linarith only [h9068, h9343, hlam]
                          · linarith only [h9066, h9342, hlam]
                        · linarith only [h2, h9341, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                · linarith only [h0, h4, h9067, h9069, h9073, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h4, h8676, h9072, hlam]
          · linarith only [h9064, h9067, h9069, hlam]
        · linarith only [h8676, h8678, h9064, h9066, h9068, hc24, hc45, hlam, hphi]
      · linarith only [h4, h8675, h9066, h9067, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
    · linarith only [h4, h8674, h9066, hc12, hc23, hlam, hphi]

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8676 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8677 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h8678 | h8678
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675 h8676 h8677 h8678
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675 h8676 h8677 h8678

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8676 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8677 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h4, h8675, h8677, hlam]

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8676 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h8677 | h8677
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675 h8676 h8677
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675 h8676 h8677

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8676 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h4, h8674, h8676, hlam]

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h8676 | h8676
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675 h8676
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675 h8676

end R2N4
