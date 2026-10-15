import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10050000 in
set_option maxHeartbeats 10050000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h9029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  rcases m.htr 0 3 5 (by decide) (by decide) with h9031 | h9031
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9032 | h9032
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9033 | h9033
      · linarith only [h0, h4, h9029, h9033, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9035 | h9035
        · linarith only [h0, h7821, h9035, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9037 | h9037
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9038 | h9038
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9039 | h9039
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9040 | h9040
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9041 | h9041
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9042 | h9042
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9043 | h9043
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9044 | h9044
                        · rcases h0bigk with h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c | h9045c
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9047 | h9047
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9048 | h9048
                              · linarith only [h0, h9048, hlam]
                              · rcases p9045_3 (m.d 0 3) (by simp) with h9050 | h9050
                                · linarith only [h1, h9050, hlam]
                                · linarith only [h4, h9050, hlam]
                            · linarith only [h0, h9047, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h1, h9038, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9045_1]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9055 | h9055
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9056 | h9056
                              · linarith only [h0, h9056, hlam]
                              · rcases p9045_3 (m.d 0 3) (by simp) with h9058 | h9058
                                · linarith only [h1, h9058, hlam]
                                · linarith only [h9030, h9058, hlam]
                            · linarith only [h2, h9055, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9062 | h9062
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9063 | h9063
                              · linarith only [h0, h9063, hlam]
                              · linarith only [h9029, h9063, hlam]
                            · linarith only [h3, h9062, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h0, hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h4, hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h7821, hlam, p9045_1]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9071 | h9071
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9072 | h9072
                              · rcases p9045_3 (m.d 0 3) (by simp) with h9073 | h9073
                                · rcases p9045_3 (m.d 0 4) (by simp) with h9074 | h9074
                                  · rcases p9045_3 (m.d 0 5) (by simp) with h9075 | h9075
                                    · linarith only [h9029, h9075, hlam]
                                    · rcases h2bigk with h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c | h9077c
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h7821, h9041, hc12, hc23, hlam, hphi, p9077_1]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h4, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h7821, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        rcases p9077_3 (m.d 0 2) (by simp) with h9082 | h9082
                                        · rcases p9077_3 (m.d 1 2) (by simp) with h9083 | h9083
                                          · linarith only [h0, h9083, hlam]
                                          · linarith only [h9037, h9083, hlam]
                                        · linarith only [h9082, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h0, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9033, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9035, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        rcases p9077_3 (m.d 0 2) (by simp) with h9091 | h9091
                                        · rcases p9077_3 (m.d 1 2) (by simp) with h9092 | h9092
                                          · rcases p9077_3 (m.d 2 3) (by simp) with h9093 | h9093
                                            · rcases p9077_3 (m.d 2 4) (by simp) with h9094 | h9094
                                              · rcases p9077_3 (m.d 2 5) (by simp) with h9095 | h9095
                                                · linarith only [h9095, hlam, p9077_0]
                                                · rcases h3bigk with h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c | h9097c
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9035, h9038, h9042, h9044, hc03, hc45, hlam, hphi, ht0b, ht5b, p9077_1, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h4, hlam, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    rcases p9097_3 (m.d 0 3) (by simp) with h9101 | h9101
                                                    · rcases p9097_3 (m.d 1 3) (by simp) with h9102 | h9102
                                                      · linarith only [h1, h9102, hlam]
                                                      · linarith only [h9038, h9102, hlam]
                                                    · linarith only [h9101, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    rcases p9097_3 (m.d 0 3) (by simp) with h9106 | h9106
                                                    · rcases p9097_3 (m.d 1 3) (by simp) with h9107 | h9107
                                                      · linarith only [h1, h9107, hlam]
                                                      · linarith only [h9039, h9107, hlam]
                                                    · linarith only [h9106, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h1, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9033, hlam, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h1, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    rcases p9097_3 (m.d 0 3) (by simp) with h9115 | h9115
                                                    · rcases p9097_3 (m.d 1 3) (by simp) with h9116 | h9116
                                                      · rcases p9097_3 (m.d 2 3) (by simp) with h9117 | h9117
                                                        · rcases p9097_3 (m.d 3 4) (by simp) with h9118 | h9118
                                                          · linarith only [h9038, h9118, hlam]
                                                          · linarith only [h9044, h9118, hlam]
                                                        · linarith only [h9042, h9117, hlam]
                                                      · linarith only [h9116, hlam, p9097_0]
                                                    · linarith only [h9031, h9115, hlam]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h3, h4, h9037, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9033, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9077_1, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    rcases p9097_3 (m.d 0 3) (by simp) with h9127 | h9127
                                                    · linarith only [h4, h9127, hlam]
                                                    · linarith only [h9030, h9127, hlam]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h3, h4, h9037, h9042, hlam, p9045_1, p9097_2]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9030, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9038, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9041, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h1, h9038, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9097_1]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9031, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9039, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9042, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [h9044, hlam, p9097_0]
                                                  · have p9097_0 := h9097c.1
                                                    have p9097_1 := h9097c.2.1
                                                    have p9097_2 := h9097c.2.2.1
                                                    have p9097_3 := h9097c.2.2.2
                                                    linarith only [hlam, p9097_0]
                                              · linarith only [h9043, h9094, hlam]
                                            · linarith only [h9042, h9093, hlam]
                                          · linarith only [h9092, hlam, p9077_0]
                                        · linarith only [h9029, h9091, hlam]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h3, h9037, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9077_1]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        rcases p9077_3 (m.d 0 2) (by simp) with h9146 | h9146
                                        · linarith only [h4, h9146, hlam]
                                        · linarith only [h0, h9146, hlam]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h3, h7821, h9037, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9077_1]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h3, h4, h9037, hlam, p9045_1, p9077_2]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h3, h9037, h9042, h9044, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9077_1]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        rcases p9077_3 (m.d 0 2) (by simp) with h9153 | h9153
                                        · linarith only [h7821, h9153, hlam]
                                        · linarith only [h0, h9153, hlam]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9041, hlam, p9077_1]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h3, h7821, h9037, hlam, p9045_1, p9077_2]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9029, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9037, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9042, hlam, p9077_1]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [h9043, hlam, p9077_0]
                                      · have p9077_0 := h9077c.1
                                        have p9077_1 := h9077c.2.1
                                        have p9077_2 := h9077c.2.2.1
                                        have p9077_3 := h9077c.2.2.2
                                        linarith only [hlam, p9077_0]
                                  · linarith only [h9032, h9074, hlam]
                                · linarith only [h9031, h9073, hlam]
                              · linarith only [h9029, h9072, hlam]
                            · linarith only [h3, h9071, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h1, hlam, p9045_1]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9169 | h9169
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9170 | h9170
                              · linarith only [h4, h9170, hlam]
                              · rcases p9045_3 (m.d 0 3) (by simp) with h9172 | h9172
                                · rcases p9045_3 (m.d 0 4) (by simp) with h9173 | h9173
                                  · linarith only [h9030, h9173, hlam]
                                  · linarith only [h7821, h9173, hlam]
                                · linarith only [h4, h9172, hlam]
                            · linarith only [h0, h9169, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9179 | h9179
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9180 | h9180
                              · linarith only [h4, h9180, hlam]
                              · rcases p9045_3 (m.d 0 3) (by simp) with h9182 | h9182
                                · rcases p9045_3 (m.d 0 4) (by simp) with h9183 | h9183
                                  · linarith only [h9030, h9183, hlam]
                                  · rcases p9045_3 (m.d 0 5) (by simp) with h9185 | h9185
                                    · linarith only [h9031, h9185, hlam]
                                    · rcases h2bigk with h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c | h9187c
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h4, h7821, h9037, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9187_1]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h4, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h7821, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h4, h7821, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9187_1]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h0, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9033, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9035, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h0, h4, h7821, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9187_1]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        rcases p9187_3 (m.d 0 2) (by simp) with h9198 | h9198
                                        · linarith only [h9198, hlam, p9187_0]
                                        · rcases p9187_3 (m.d 1 2) (by simp) with h9200 | h9200
                                          · linarith only [h9033, h9200, hlam]
                                          · rcases p9187_3 (m.d 2 3) (by simp) with h9202 | h9202
                                            · rcases p9187_3 (m.d 2 4) (by simp) with h9203 | h9203
                                              · linarith only [h9041, h9203, hlam]
                                              · linarith only [h7821, h9203, hlam]
                                            · linarith only [h9202, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        rcases p9187_3 (m.d 0 2) (by simp) with h9207 | h9207
                                        · linarith only [h4, h9207, hlam]
                                        · linarith only [h0, h9207, hlam]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h7821, hc02, hc23, hlam, hphi, p9187_1]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h2, h4, h9035, h9037, hlam, p9045_1, p9187_2]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        rcases p9187_3 (m.d 0 2) (by simp) with h9213 | h9213
                                        · linarith only [h9213, hlam, p9187_0]
                                        · rcases p9187_3 (m.d 1 2) (by simp) with h9215 | h9215
                                          · linarith only [h9035, h9215, hlam]
                                          · rcases p9187_3 (m.d 2 3) (by simp) with h9217 | h9217
                                            · rcases p9187_3 (m.d 2 4) (by simp) with h9218 | h9218
                                              · rcases p9187_3 (m.d 2 5) (by simp) with h9219 | h9219
                                                · linarith only [h9043, h9219, hlam]
                                                · rcases h3bigk with h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c | h9221c
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h1, h9038, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h4, hlam, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    rcases p9221_3 (m.d 0 3) (by simp) with h9225 | h9225
                                                    · rcases p9221_3 (m.d 1 3) (by simp) with h9226 | h9226
                                                      · linarith only [h1, h9226, hlam]
                                                      · linarith only [h9038, h9226, hlam]
                                                    · linarith only [h9225, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h2, h9035, h9037, h9042, hlam, p9045_1, p9221_2]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h1, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9033, hlam, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h1, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    rcases p9221_3 (m.d 0 3) (by simp) with h9235 | h9235
                                                    · rcases p9221_3 (m.d 1 3) (by simp) with h9236 | h9236
                                                      · rcases p9221_3 (m.d 2 3) (by simp) with h9237 | h9237
                                                        · rcases p9221_3 (m.d 3 4) (by simp) with h9238 | h9238
                                                          · linarith only [h9038, h9238, hlam]
                                                          · linarith only [h9044, h9238, hlam]
                                                        · linarith only [h9042, h9237, hlam]
                                                      · linarith only [h9236, hlam, p9221_0]
                                                    · linarith only [h9031, h9235, hlam]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9045_1, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9038, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    rcases p9221_3 (m.d 0 3) (by simp) with h9247 | h9247
                                                    · linarith only [h4, h9247, hlam]
                                                    · linarith only [h9030, h9247, hlam]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h2, h4, h9035, h9037, h9042, hlam, p9045_1, p9221_2]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9030, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9038, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9041, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h1, h9038, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9221_1]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9031, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9039, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9042, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [h9044, hlam, p9221_0]
                                                  · have p9221_0 := h9221c.1
                                                    have p9221_1 := h9221c.2.1
                                                    have p9221_2 := h9221c.2.2.1
                                                    have p9221_3 := h9221c.2.2.2
                                                    linarith only [hlam, p9221_0]
                                              · linarith only [h9218, hlam, p9187_0]
                                            · linarith only [h4, h9217, hlam]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        rcases p9187_3 (m.d 0 2) (by simp) with h9263 | h9263
                                        · linarith only [h7821, h9263, hlam]
                                        · linarith only [h0, h9263, hlam]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9041, hlam, p9187_1]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        rcases p9187_3 (m.d 0 2) (by simp) with h9268 | h9268
                                        · linarith only [h7821, h9268, hlam]
                                        · linarith only [h9029, h9268, hlam]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9029, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9037, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9042, hlam, p9187_1]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [h9043, hlam, p9187_0]
                                      · have p9187_0 := h9187c.1
                                        have p9187_1 := h9187c.2.1
                                        have p9187_2 := h9187c.2.2.1
                                        have p9187_3 := h9187c.2.2.2
                                        linarith only [hlam, p9187_0]
                                · linarith only [h9030, h9182, hlam]
                            · linarith only [h2, h9179, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9278 | h9278
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9279 | h9279
                              · linarith only [h4, h9279, hlam]
                              · linarith only [h9029, h9279, hlam]
                            · linarith only [h3, h9278, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h2, hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9284 | h9284
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9285 | h9285
                              · linarith only [h7821, h9285, hlam]
                              · rcases p9045_3 (m.d 0 3) (by simp) with h9287 | h9287
                                · rcases p9045_3 (m.d 0 4) (by simp) with h9288 | h9288
                                  · rcases p9045_3 (m.d 0 5) (by simp) with h9289 | h9289
                                    · linarith only [h9032, h9289, hlam]
                                    · rcases h2bigk with h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c | h9291c
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9037, h9042, h9044, hc04, hc45, hlam, hphi, ht0b, ht5b, p9045_1, p9291_1]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h4, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h7821, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h7821, h9042, h9044, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9291_1]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h0, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9033, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9035, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h0, h7821, h9042, h9044, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9291_1]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        rcases p9291_3 (m.d 0 2) (by simp) with h9302 | h9302
                                        · linarith only [h9302, hlam, p9291_0]
                                        · rcases p9291_3 (m.d 1 2) (by simp) with h9304 | h9304
                                          · linarith only [h9033, h9304, hlam]
                                          · rcases p9291_3 (m.d 2 3) (by simp) with h9306 | h9306
                                            · rcases p9291_3 (m.d 2 4) (by simp) with h9307 | h9307
                                              · linarith only [h9041, h9307, hlam]
                                              · linarith only [h7821, h9307, hlam]
                                            · linarith only [h9306, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        rcases p9291_3 (m.d 0 2) (by simp) with h9311 | h9311
                                        · linarith only [h4, h9311, hlam]
                                        · linarith only [h0, h9311, hlam]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h7821, hc02, hc23, hlam, hphi, p9291_1]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h0, h4, h9030, h9037, hlam, p9045_1, p9291_2]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        rcases p9291_3 (m.d 0 2) (by simp) with h9317 | h9317
                                        · linarith only [h9317, hlam, p9291_0]
                                        · rcases p9291_3 (m.d 1 2) (by simp) with h9319 | h9319
                                          · linarith only [h9035, h9319, hlam]
                                          · rcases p9291_3 (m.d 2 3) (by simp) with h9321 | h9321
                                            · rcases p9291_3 (m.d 2 4) (by simp) with h9322 | h9322
                                              · rcases p9291_3 (m.d 2 5) (by simp) with h9323 | h9323
                                                · linarith only [h9043, h9323, hlam]
                                                · rcases h3bigk with h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c | h9325c
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9038, h9044, hc03, hc45, hlam, hphi, ht0b, ht5b, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h4, hlam, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    rcases p9325_3 (m.d 0 3) (by simp) with h9329 | h9329
                                                    · rcases p9325_3 (m.d 1 3) (by simp) with h9330 | h9330
                                                      · linarith only [h1, h9330, hlam]
                                                      · linarith only [h9038, h9330, hlam]
                                                    · linarith only [h9329, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h0, h9030, h9037, h9042, hlam, p9045_1, p9325_2]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h1, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9033, hlam, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h1, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    rcases p9325_3 (m.d 0 3) (by simp) with h9339 | h9339
                                                    · rcases p9325_3 (m.d 1 3) (by simp) with h9340 | h9340
                                                      · rcases p9325_3 (m.d 2 3) (by simp) with h9341 | h9341
                                                        · rcases p9325_3 (m.d 3 4) (by simp) with h9342 | h9342
                                                          · linarith only [h9038, h9342, hlam]
                                                          · linarith only [h9044, h9342, hlam]
                                                        · linarith only [h9042, h9341, hlam]
                                                      · linarith only [h9340, hlam, p9325_0]
                                                    · linarith only [h9031, h9339, hlam]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h0, h9030, h9037, h9042, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9045_1, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9038, h9044, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    rcases p9325_3 (m.d 0 3) (by simp) with h9351 | h9351
                                                    · linarith only [h4, h9351, hlam]
                                                    · linarith only [h9030, h9351, hlam]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h0, h4, h9030, h9037, h9042, hlam, p9045_1, p9325_2]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9030, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9038, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9041, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h1, h9038, h9044, hc01, hc45, hlam, hphi, ht0b, ht5b, p9325_1]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9031, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9039, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9042, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [h9044, hlam, p9325_0]
                                                  · have p9325_0 := h9325c.1
                                                    have p9325_1 := h9325c.2.1
                                                    have p9325_2 := h9325c.2.2.1
                                                    have p9325_3 := h9325c.2.2.2
                                                    linarith only [hlam, p9325_0]
                                              · linarith only [h9322, hlam, p9291_0]
                                            · linarith only [h4, h9321, hlam]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        rcases p9291_3 (m.d 0 2) (by simp) with h9367 | h9367
                                        · linarith only [h7821, h9367, hlam]
                                        · linarith only [h0, h9367, hlam]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9041, hlam, p9291_1]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h0, h7821, h9037, hlam, p9045_1, p9291_2]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9029, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9037, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9042, hlam, p9291_1]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [h9043, hlam, p9291_0]
                                      · have p9291_0 := h9291c.1
                                        have p9291_1 := h9291c.2.1
                                        have p9291_2 := h9291c.2.2.1
                                        have p9291_3 := h9291c.2.2.2
                                        linarith only [hlam, p9291_0]
                                  · linarith only [h7821, h9288, hlam]
                                · linarith only [h4, h9287, hlam]
                            · linarith only [h0, h9284, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h9030, hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            rcases p9045_3 (m.d 0 1) (by simp) with h9383 | h9383
                            · rcases p9045_3 (m.d 0 2) (by simp) with h9384 | h9384
                              · linarith only [h7821, h9384, hlam]
                              · linarith only [h9029, h9384, hlam]
                            · linarith only [h3, h9383, hlam]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h3, hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h9029, hlam, p9045_1]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h9031, hlam, p9045_0]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [h9032, hlam, p9045_1]
                          · have p9045_0 := h9045c.1
                            have p9045_1 := h9045c.2.1
                            have p9045_2 := h9045c.2.2.1
                            have p9045_3 := h9045c.2.2.2
                            linarith only [hlam, p9045_0]
                        · rcases h0bigk with h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c | h9393c
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h0, h9037, h9043, h9044, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h2, h9030, h9035, h9037, h9043, h9044, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h2, h9035, h9037, h9043, h9044, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            rcases p9393_3 (m.d 0 1) (by simp) with h9398 | h9398
                            · rcases p9393_3 (m.d 0 2) (by simp) with h9399 | h9399
                              · linarith only [h0, h9399, hlam]
                              · linarith only [h9029, h9399, hlam]
                            · linarith only [h3, h9398, hlam]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h0, hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h4, hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h7821, hlam, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h3, h7821, h9037, h9043, h9044, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h1, hlam, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h0, h9037, h9043, h9044, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h2, h4, h9035, h9037, h9043, h9044, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            rcases p9393_3 (m.d 0 1) (by simp) with h9412 | h9412
                            · rcases p9393_3 (m.d 0 2) (by simp) with h9413 | h9413
                              · linarith only [h4, h9413, hlam]
                              · linarith only [h9029, h9413, hlam]
                            · linarith only [h3, h9412, hlam]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h2, hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h0, h9037, h9043, h9044, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h9030, hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            rcases p9393_3 (m.d 0 1) (by simp) with h9421 | h9421
                            · rcases p9393_3 (m.d 0 2) (by simp) with h9422 | h9422
                              · linarith only [h7821, h9422, hlam]
                              · linarith only [h9029, h9422, hlam]
                            · linarith only [h3, h9421, hlam]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h3, hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h9029, hlam, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h9031, hlam, p9393_0]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [h9032, hlam, p9393_1]
                          · have p9393_0 := h9393c.1
                            have p9393_1 := h9393c.2.1
                            have p9393_2 := h9393c.2.2.1
                            have p9393_3 := h9393c.2.2.2
                            linarith only [hlam, p9393_0]
                      · linarith only [h0, h7821, h9032, h9037, h9043, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h9031, h9042, hlam]
                  · linarith only [h4, h9030, h9041, hlam]
                · linarith only [h9035, h9037, h9040, hlam]
              · linarith only [h9035, h9037, h9038, h9039, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9436 | h9436
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9437 | h9437
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9438 | h9438
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9439 | h9439
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9440 | h9440
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9441 | h9441
                        · rcases h0bigk with h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c | h9442c
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9444 | h9444
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9445 | h9445
                              · linarith only [h0, h9445, hlam]
                              · rcases p9442_3 (m.d 0 3) (by simp) with h9447 | h9447
                                · linarith only [h1, h9447, hlam]
                                · linarith only [h4, h9447, hlam]
                            · linarith only [h0, h9444, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h9030, h9038, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h9030, h9033, h9037, h9038, h9439, h9441, hc01, hc45, hlam, hphi, ht0b, ht5b, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9453 | h9453
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9454 | h9454
                              · linarith only [h0, h9454, hlam]
                              · linarith only [h9029, h9454, hlam]
                            · linarith only [h3, h9453, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h0, hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h4, hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h7821, hlam, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9462 | h9462
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9463 | h9463
                              · rcases p9442_3 (m.d 0 3) (by simp) with h9464 | h9464
                                · rcases p9442_3 (m.d 0 4) (by simp) with h9465 | h9465
                                  · rcases p9442_3 (m.d 0 5) (by simp) with h9466 | h9466
                                    · linarith only [h9029, h9466, hlam]
                                    · rcases h2bigk with h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c | h9468c
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h7821, h9037, h9438, h9439, h9441, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h4, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h7821, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        rcases p9468_3 (m.d 0 2) (by simp) with h9473 | h9473
                                        · rcases p9468_3 (m.d 1 2) (by simp) with h9474 | h9474
                                          · linarith only [h0, h9474, hlam]
                                          · linarith only [h9037, h9474, hlam]
                                        · linarith only [h9473, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h0, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9033, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9035, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9030, h9033, h9038, h9439, h9441, hc03, hc45, hlam, hphi, ht0b, ht5b, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9442_1, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        rcases p9468_3 (m.d 0 2) (by simp) with h9484 | h9484
                                        · linarith only [h4, h9484, hlam]
                                        · linarith only [h0, h9484, hlam]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h3, h7821, h9037, h9439, h9441, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9442_1, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h3, h4, h9037, hlam, p9442_1, p9468_2]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p9442_1, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        rcases p9468_3 (m.d 0 2) (by simp) with h9491 | h9491
                                        · linarith only [h7821, h9491, hlam]
                                        · linarith only [h0, h9491, hlam]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9438, hlam, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h3, h7821, h9037, hlam, p9442_1, p9468_2]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9029, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9037, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9439, hlam, p9468_1]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [h9440, hlam, p9468_0]
                                      · have p9468_0 := h9468c.1
                                        have p9468_1 := h9468c.2.1
                                        have p9468_2 := h9468c.2.2.1
                                        have p9468_3 := h9468c.2.2.2
                                        linarith only [hlam, p9468_0]
                                  · linarith only [h9032, h9465, hlam]
                                · linarith only [h9031, h9464, hlam]
                              · linarith only [h9029, h9463, hlam]
                            · linarith only [h3, h9462, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h1, hlam, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9507 | h9507
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9508 | h9508
                              · linarith only [h4, h9508, hlam]
                              · rcases p9442_3 (m.d 0 3) (by simp) with h9510 | h9510
                                · rcases p9442_3 (m.d 0 4) (by simp) with h9511 | h9511
                                  · linarith only [h9030, h9511, hlam]
                                  · linarith only [h7821, h9511, hlam]
                                · linarith only [h4, h9510, hlam]
                            · linarith only [h0, h9507, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h4, h9030, h9033, h9038, hc12, hc23, hlam, hphi, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9518 | h9518
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9519 | h9519
                              · linarith only [h4, h9519, hlam]
                              · linarith only [h9029, h9519, hlam]
                            · linarith only [h3, h9518, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h2, hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9524 | h9524
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9525 | h9525
                              · linarith only [h7821, h9525, hlam]
                              · rcases p9442_3 (m.d 0 3) (by simp) with h9527 | h9527
                                · rcases p9442_3 (m.d 0 4) (by simp) with h9528 | h9528
                                  · rcases p9442_3 (m.d 0 5) (by simp) with h9529 | h9529
                                    · linarith only [h9032, h9529, hlam]
                                    · rcases h2bigk with h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c | h9531c
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h4, h9030, h9037, h9439, h9441, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9442_1, p9531_1]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h4, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h7821, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h4, h9030, h9439, h9441, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9442_1, p9531_1]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h0, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9033, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9035, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h0, h4, h9030, h9439, h9441, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9442_1, p9531_1]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        rcases p9531_3 (m.d 0 2) (by simp) with h9542 | h9542
                                        · linarith only [h9542, hlam, p9531_0]
                                        · rcases p9531_3 (m.d 1 2) (by simp) with h9544 | h9544
                                          · linarith only [h9033, h9544, hlam]
                                          · rcases p9531_3 (m.d 2 3) (by simp) with h9546 | h9546
                                            · rcases p9531_3 (m.d 2 4) (by simp) with h9547 | h9547
                                              · linarith only [h9438, h9547, hlam]
                                              · linarith only [h7821, h9547, hlam]
                                            · linarith only [h9546, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        rcases p9531_3 (m.d 0 2) (by simp) with h9551 | h9551
                                        · linarith only [h4, h9551, hlam]
                                        · linarith only [h0, h9551, hlam]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h7821, hc02, hc23, hlam, hphi, p9442_1, p9531_1]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h4, h9030, h9033, h9037, h9038, hlam, p9531_2]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        rcases p9531_3 (m.d 0 2) (by simp) with h9557 | h9557
                                        · linarith only [h9557, hlam, p9531_0]
                                        · rcases p9531_3 (m.d 1 2) (by simp) with h9559 | h9559
                                          · linarith only [h9035, h9559, hlam]
                                          · rcases p9531_3 (m.d 2 3) (by simp) with h9561 | h9561
                                            · rcases p9531_3 (m.d 2 4) (by simp) with h9562 | h9562
                                              · rcases p9531_3 (m.d 2 5) (by simp) with h9563 | h9563
                                                · linarith only [h9440, h9563, hlam]
                                                · rcases h3bigk with h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    rcases p9565_3 (m.d 0 3) (by simp) with h9567 | h9567
                                                    · rcases p9565_3 (m.d 1 3) (by simp) with h9568 | h9568
                                                      · linarith only [h1, h9568, hlam]
                                                      · rcases p9565_3 (m.d 2 3) (by simp) with h9570 | h9570
                                                        · rcases p9565_3 (m.d 3 4) (by simp) with h9571 | h9571
                                                          · linarith only [h9030, h9571, hlam]
                                                          · linarith only [h9038, h9571, hlam]
                                                        · linarith only [h9033, h9570, hlam]
                                                    · linarith only [h1, h9567, hlam]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h4, hlam, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9033, h9037, h9038, h9439, h9441, hc03, hc45, hlam, hphi, ht0b, ht5b, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9030, h9033, h9037, h9038, h9439, hlam, p9565_2]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h1, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9033, hlam, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9038, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9030, h9038, h9441, hc03, hc45, hlam, hphi, ht0b, ht5b, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9030, h9038, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    rcases p9565_3 (m.d 0 3) (by simp) with h9585 | h9585
                                                    · linarith only [h4, h9585, hlam]
                                                    · linarith only [h1, h9585, hlam]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9033, h9037, h9038, h9439, h9441, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h0, h4, h9030, h9037, h9439, hlam, p9442_1, p9565_2]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9030, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9030, h9033, h9037, h9439, h9441, hc03, hc45, hlam, hphi, ht0b, ht5b, p9565_1]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9438, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    rcases p9565_3 (m.d 0 3) (by simp) with h9595 | h9595
                                                    · rcases p9565_3 (m.d 1 3) (by simp) with h9596 | h9596
                                                      · linarith only [h9038, h9596, hlam]
                                                      · linarith only [h9436, h9596, hlam]
                                                    · linarith only [h9031, h9595, hlam]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9031, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9436, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9439, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [h9441, hlam, p9565_0]
                                                  · have p9565_0 := h9565c.1
                                                    have p9565_1 := h9565c.2.1
                                                    have p9565_2 := h9565c.2.2.1
                                                    have p9565_3 := h9565c.2.2.2
                                                    linarith only [hlam, p9565_0]
                                              · linarith only [h9562, hlam, p9531_0]
                                            · linarith only [h4, h9561, hlam]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        rcases p9531_3 (m.d 0 2) (by simp) with h9607 | h9607
                                        · linarith only [h7821, h9607, hlam]
                                        · linarith only [h0, h9607, hlam]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9438, hlam, p9531_1]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h0, h7821, h9037, hlam, p9442_1, p9531_2]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9029, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9037, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9439, hlam, p9531_1]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [h9440, hlam, p9531_0]
                                      · have p9531_0 := h9531c.1
                                        have p9531_1 := h9531c.2.1
                                        have p9531_2 := h9531c.2.2.1
                                        have p9531_3 := h9531c.2.2.2
                                        linarith only [hlam, p9531_0]
                                  · linarith only [h7821, h9528, hlam]
                                · linarith only [h4, h9527, hlam]
                            · linarith only [h0, h9524, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h9030, hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            rcases p9442_3 (m.d 0 1) (by simp) with h9623 | h9623
                            · rcases p9442_3 (m.d 0 2) (by simp) with h9624 | h9624
                              · linarith only [h7821, h9624, hlam]
                              · linarith only [h9029, h9624, hlam]
                            · linarith only [h3, h9623, hlam]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h3, hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h9029, hlam, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h9031, hlam, p9442_0]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [h9032, hlam, p9442_1]
                          · have p9442_0 := h9442c.1
                            have p9442_1 := h9442c.2.1
                            have p9442_2 := h9442c.2.2.1
                            have p9442_3 := h9442c.2.2.2
                            linarith only [hlam, p9442_0]
                        · linarith only [h4, h9030, h9032, h9033, h9037, h9038, h9439, h9441, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h3, h7821, h9037, h9437, h9439, h9440, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h9030, h9033, h9037, h9038, h9439, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h4, h9030, h9438, hlam]
                · linarith only [h9033, h9037, h9038, h9437, hlam]
              · linarith only [h9033, h9037, h9436, hlam]
          · linarith only [h7821, h9029, h9037, hc12, hc24, hlam, hphi]
    · linarith only [h7821, h9029, h9032, hlam]
  · linarith only [h4, h9029, h9031, hlam]

end R2N4
