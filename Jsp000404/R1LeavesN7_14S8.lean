import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8058 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8059 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 5 (by decide) (by decide) with h8060 | h8060
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8061 | h8061
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8062 | h8062
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8063 | h8063
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8064 | h8064
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8065 | h8065
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8066 | h8066
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8067 | h8067
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8068 | h8068
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8069 | h8069
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8070 | h8070
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8071 | h8071
                        · linarith only [h8056, h8068, h8071, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h8056, h8068, h8070, h8071, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8074 | h8074
                        · linarith only [h8068, h8070, h8074, hlam]
                        · rcases h0bigk with h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c | h8076c
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h0, hlam, p8076_1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h4610, hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h6681, hlam, p8076_1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h7494, hlam, p8076_1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            rcases p8076_3 (m.d 0 1) (by simp) with h8082 | h8082
                            · linarith only [h0, h8082, hlam]
                            · rcases p8076_3 (m.d 0 2) (by simp) with h8084 | h8084
                              · rcases p8076_3 (m.d 0 3) (by simp) with h8085 | h8085
                                · linarith only [h8056, h8085, hlam]
                                · linarith only [h4610, h8085, hlam]
                              · linarith only [h0, h8084, hlam]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8059, h8061, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8076_1, u0elo1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8061, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8076_1, u0elo1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8061, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8076_1, u0elo1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            rcases p8076_3 (m.d 0 1) (by simp) with h8093 | h8093
                            · linarith only [h4610, h8093, hlam]
                            · rcases p8076_3 (m.d 0 2) (by simp) with h8095 | h8095
                              · rcases p8076_3 (m.d 0 3) (by simp) with h8096 | h8096
                                · rcases p8076_3 (m.d 0 4) (by simp) with h8097 | h8097
                                  · linarith only [h8059, h8097, hlam]
                                  · linarith only [h6681, h8097, hlam]
                                · linarith only [h4610, h8096, hlam]
                              · linarith only [h0, h8095, hlam]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8056, hlam, p8076_1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8061, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8076_1, u0elo2]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8056, h8061, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8076_1, u0elo1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            rcases p8076_3 (m.d 0 1) (by simp) with h8106 | h8106
                            · linarith only [h6681, h8106, hlam]
                            · rcases p8076_3 (m.d 0 2) (by simp) with h8108 | h8108
                              · rcases p8076_3 (m.d 0 3) (by simp) with h8109 | h8109
                                · rcases p8076_3 (m.d 0 4) (by simp) with h8110 | h8110
                                  · rcases p8076_3 (m.d 0 5) (by simp) with h8111 | h8111
                                    · linarith only [h8061, h8111, hlam]
                                    · linarith only [h7494, h8111, hlam]
                                  · linarith only [h6681, h8110, hlam]
                                · linarith only [h4610, h8109, hlam]
                              · linarith only [h0, h8108, hlam]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8057, hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8059, hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8061, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8076_1, u0elo3]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            rcases p8076_3 (m.d 0 1) (by simp) with h8121 | h8121
                            · linarith only [h7494, h8121, hlam]
                            · rcases p8076_3 (m.d 0 2) (by simp) with h8123 | h8123
                              · rcases p8076_3 (m.d 0 3) (by simp) with h8124 | h8124
                                · rcases p8076_3 (m.d 0 4) (by simp) with h8125 | h8125
                                  · rcases p8076_3 (m.d 0 5) (by simp) with h8126 | h8126
                                    · rcases h2bigk with h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c | h8127c
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h0, hlam, p8127_1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8069, hc35, hlam, hphi, ht0b, ht5b, p8127_1, u0elo1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        rcases p8127_3 (m.d 0 2) (by simp) with h8131 | h8131
                                        · rcases p8127_3 (m.d 1 2) (by simp) with h8132 | h8132
                                          · rcases p8127_3 (m.d 2 3) (by simp) with h8133 | h8133
                                            · linarith only [h8056, h8133, hlam]
                                            · linarith only [h8068, h8133, hlam]
                                          · linarith only [h8063, h8132, hlam]
                                        · linarith only [h8131, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        rcases p8127_3 (m.d 0 2) (by simp) with h8138 | h8138
                                        · rcases p8127_3 (m.d 1 2) (by simp) with h8139 | h8139
                                          · rcases p8127_3 (m.d 2 3) (by simp) with h8140 | h8140
                                            · linarith only [h8056, h8140, hlam]
                                            · linarith only [h8069, h8140, hlam]
                                          · linarith only [h8064, h8139, hlam]
                                        · linarith only [h8138, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8056, h8069, h8074, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8127_1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        rcases p8127_3 (m.d 0 2) (by simp) with h8147 | h8147
                                        · linarith only [h0, h8147, hlam]
                                        · linarith only [h8056, h8147, hlam]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        rcases p8127_3 (m.d 0 2) (by simp) with h8150 | h8150
                                        · linarith only [h0, h8150, hlam]
                                        · linarith only [h8057, h8150, hlam]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        rcases p8127_3 (m.d 0 2) (by simp) with h8153 | h8153
                                        · linarith only [h0, h8153, hlam]
                                        · linarith only [h8058, h8153, hlam]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8056, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8062, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8056, h8068, hc34, hlam, hphi, ht0b, ht45, ht5b, p8127_1, u0elo1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8056, h8068, h8070, hc34, hlam, hphi, ht0b, ht45, ht5b, p8127_1, u0elo1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8057, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8063, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8068, hlam, p8127_1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8070, hlam, p8127_1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8058, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8064, hlam, p8127_0]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8069, hlam, p8127_1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [h8058, h8068, hc34, hlam, hphi, ht0b, ht45, ht5b, p8127_1, u0elo1]
                                      · have p8127_0 := h8127c.1
                                        have p8127_1 := h8127c.2.1
                                        have p8127_2 := h8127c.2.2.1
                                        have p8127_3 := h8127c.2.2.2
                                        linarith only [hlam, p8127_0]
                                    · linarith only [h7494, h8126, hlam]
                                  · linarith only [h6681, h8125, hlam]
                                · linarith only [h4610, h8124, hlam]
                              · linarith only [h0, h8123, hlam]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8058, hlam, p8076_1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8060, hlam, p8076_0]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [h8061, hlam, p8076_1]
                          · have p8076_0 := h8076c.1
                            have p8076_1 := h8076c.2.1
                            have p8076_2 := h8076c.2.2.1
                            have p8076_3 := h8076c.2.2.2
                            linarith only [hlam, p8076_0]
                    · linarith only [h8060, h8068, h8069, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8180 | h8180
                    · linarith only [h8056, h8059, h8068, h8180, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8182 | h8182
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8183 | h8183
                        · rcases h0bigk with h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c | h8184c
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h0, hlam, p8184_1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h4610, hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h6681, hlam, p8184_1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h7494, hlam, p8184_1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            rcases p8184_3 (m.d 0 1) (by simp) with h8190 | h8190
                            · linarith only [h0, h8190, hlam]
                            · rcases p8184_3 (m.d 0 2) (by simp) with h8192 | h8192
                              · rcases p8184_3 (m.d 0 3) (by simp) with h8193 | h8193
                                · linarith only [h8056, h8193, hlam]
                                · linarith only [h4610, h8193, hlam]
                              · linarith only [h0, h8192, hlam]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8059, h8180, h8183, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8184_1, u0elo1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8057, h8182, hc45, hlam, hphi, ht0b, ht5b, p8184_1, u0elo1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8060, h8180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8184_1, u0elo1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            rcases p8184_3 (m.d 0 1) (by simp) with h8201 | h8201
                            · linarith only [h4610, h8201, hlam]
                            · rcases p8184_3 (m.d 0 2) (by simp) with h8203 | h8203
                              · rcases p8184_3 (m.d 0 3) (by simp) with h8204 | h8204
                                · rcases p8184_3 (m.d 0 4) (by simp) with h8205 | h8205
                                  · linarith only [h8059, h8205, hlam]
                                  · linarith only [h6681, h8205, hlam]
                                · linarith only [h4610, h8204, hlam]
                              · linarith only [h0, h8203, hlam]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8056, hlam, p8184_1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8059, h8180, h8183, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8184_1, u0elo2]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8056, h8060, h8180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8184_1, u0elo1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            rcases p8184_3 (m.d 0 1) (by simp) with h8214 | h8214
                            · linarith only [h6681, h8214, hlam]
                            · rcases p8184_3 (m.d 0 2) (by simp) with h8216 | h8216
                              · rcases p8184_3 (m.d 0 3) (by simp) with h8217 | h8217
                                · rcases p8184_3 (m.d 0 4) (by simp) with h8218 | h8218
                                  · rcases p8184_3 (m.d 0 5) (by simp) with h8219 | h8219
                                    · linarith only [h8061, h8219, hlam]
                                    · linarith only [h7494, h8219, hlam]
                                  · linarith only [h6681, h8218, hlam]
                                · linarith only [h4610, h8217, hlam]
                              · linarith only [h0, h8216, hlam]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8057, hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8059, hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8060, h8180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8184_1, u0elo3]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            rcases p8184_3 (m.d 0 1) (by simp) with h8229 | h8229
                            · linarith only [h7494, h8229, hlam]
                            · rcases p8184_3 (m.d 0 2) (by simp) with h8231 | h8231
                              · rcases p8184_3 (m.d 0 3) (by simp) with h8232 | h8232
                                · rcases p8184_3 (m.d 0 4) (by simp) with h8233 | h8233
                                  · rcases p8184_3 (m.d 0 5) (by simp) with h8234 | h8234
                                    · rcases h2bigk with h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c | h8235c
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h0, hlam, p8235_1]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        rcases p8235_3 (m.d 0 2) (by simp) with h8238 | h8238
                                        · rcases p8235_3 (m.d 1 2) (by simp) with h8239 | h8239
                                          · rcases p8235_3 (m.d 2 3) (by simp) with h8240 | h8240
                                            · linarith only [h8240, hlam, p8235_0]
                                            · rcases p8235_3 (m.d 2 4) (by simp) with h8242 | h8242
                                              · linarith only [h8057, h8242, hlam]
                                              · linarith only [h8068, h8242, hlam]
                                          · linarith only [h8062, h8239, hlam]
                                        · linarith only [h8238, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8182, hc45, hlam, hphi, ht0b, ht5b, p8235_1, u0elo1]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        rcases p8235_3 (m.d 0 2) (by simp) with h8248 | h8248
                                        · rcases p8235_3 (m.d 1 2) (by simp) with h8249 | h8249
                                          · rcases p8235_3 (m.d 2 3) (by simp) with h8250 | h8250
                                            · linarith only [h8056, h8250, hlam]
                                            · rcases p8235_3 (m.d 2 4) (by simp) with h8252 | h8252
                                              · linarith only [h8057, h8252, hlam]
                                              · linarith only [h8182, h8252, hlam]
                                          · linarith only [h8064, h8249, hlam]
                                        · linarith only [h8248, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8057, h8182, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8235_1]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        rcases p8235_3 (m.d 0 2) (by simp) with h8259 | h8259
                                        · linarith only [h0, h8259, hlam]
                                        · linarith only [h8056, h8259, hlam]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        rcases p8235_3 (m.d 0 2) (by simp) with h8262 | h8262
                                        · linarith only [h0, h8262, hlam]
                                        · linarith only [h8057, h8262, hlam]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        rcases p8235_3 (m.d 0 2) (by simp) with h8265 | h8265
                                        · linarith only [h0, h8265, hlam]
                                        · linarith only [h8058, h8265, hlam]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8056, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8062, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8068, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8180, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8057, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8063, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8235_1, u0elo1]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8056, h8059, h8068, h8180, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8235_1, u0elo1]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8058, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8064, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8235_1, u0elo1]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [h8182, hlam, p8235_0]
                                      · have p8235_0 := h8235c.1
                                        have p8235_1 := h8235c.2.1
                                        have p8235_2 := h8235c.2.2.1
                                        have p8235_3 := h8235c.2.2.2
                                        linarith only [hlam, p8235_0]
                                    · linarith only [h7494, h8234, hlam]
                                  · linarith only [h6681, h8233, hlam]
                                · linarith only [h4610, h8232, hlam]
                              · linarith only [h0, h8231, hlam]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8058, hlam, p8184_1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8060, hlam, p8184_0]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [h8061, hlam, p8184_1]
                          · have p8184_0 := h8184c.1
                            have p8184_1 := h8184c.2.1
                            have p8184_2 := h8184c.2.2.1
                            have p8184_3 := h8184c.2.2.2
                            linarith only [hlam, p8184_0]
                        · linarith only [h8056, h8059, h8061, h8068, h8183, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8292 | h8292
                        · linarith only [h8056, h8059, h8182, h8292, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h8056, h8059, h8061, h8068, h8292, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h6681, h8061, h8067, hlam]
              · linarith only [h4610, h8060, h8066, hlam]
            · linarith only [h4610, h8059, h8065, hlam]
          · linarith only [h0, h8058, h8064, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h8057, h8063, hlam]
      · linarith only [h0, h8056, h8062, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8301 | h8301
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8302 | h8302
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8303 | h8303
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8304 | h8304
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8305 | h8305
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8306 | h8306
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8307 | h8307
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8308 | h8308
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8309 | h8309
                      · linarith only [h8057, h8061, h8309, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8311 | h8311
                        · linarith only [h8056, h8061, h8307, h8311, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases h0bigk with h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c | h8313c
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h0, hlam, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h4610, hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h6681, hlam, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h7494, hlam, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            rcases p8313_3 (m.d 0 1) (by simp) with h8319 | h8319
                            · linarith only [h0, h8319, hlam]
                            · rcases p8313_3 (m.d 0 2) (by simp) with h8321 | h8321
                              · rcases p8313_3 (m.d 0 3) (by simp) with h8322 | h8322
                                · linarith only [h8056, h8322, hlam]
                                · linarith only [h4610, h8322, hlam]
                              · linarith only [h0, h8321, hlam]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8059, hc34, hlam, hphi, ht0b, ht45, ht5b, p8313_1, u0elo1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            rcases p8313_3 (m.d 0 1) (by simp) with h8328 | h8328
                            · linarith only [h0, h8328, hlam]
                            · rcases p8313_3 (m.d 0 2) (by simp) with h8330 | h8330
                              · rcases p8313_3 (m.d 0 3) (by simp) with h8331 | h8331
                                · linarith only [h8056, h8331, hlam]
                                · linarith only [h8059, h8331, hlam]
                              · linarith only [h8057, h8330, hlam]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            rcases p8313_3 (m.d 0 1) (by simp) with h8335 | h8335
                            · linarith only [h0, h8335, hlam]
                            · rcases p8313_3 (m.d 0 2) (by simp) with h8337 | h8337
                              · rcases p8313_3 (m.d 0 3) (by simp) with h8338 | h8338
                                · linarith only [h8056, h8338, hlam]
                                · linarith only [h8060, h8338, hlam]
                              · linarith only [h8058, h8337, hlam]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            rcases p8313_3 (m.d 0 1) (by simp) with h8342 | h8342
                            · linarith only [h4610, h8342, hlam]
                            · rcases p8313_3 (m.d 0 2) (by simp) with h8344 | h8344
                              · rcases p8313_3 (m.d 0 3) (by simp) with h8345 | h8345
                                · rcases p8313_3 (m.d 0 4) (by simp) with h8346 | h8346
                                  · linarith only [h8059, h8346, hlam]
                                  · linarith only [h6681, h8346, hlam]
                                · linarith only [h4610, h8345, hlam]
                              · linarith only [h0, h8344, hlam]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8056, hlam, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            rcases p8313_3 (m.d 0 1) (by simp) with h8353 | h8353
                            · linarith only [h4610, h8353, hlam]
                            · rcases p8313_3 (m.d 0 2) (by simp) with h8355 | h8355
                              · rcases p8313_3 (m.d 0 3) (by simp) with h8356 | h8356
                                · rcases p8313_3 (m.d 0 4) (by simp) with h8357 | h8357
                                  · linarith only [h8059, h8357, hlam]
                                  · rcases p8313_3 (m.d 0 5) (by simp) with h8359 | h8359
                                    · linarith only [h8060, h8359, hlam]
                                    · linarith only [h8061, h8359, hlam]
                                · linarith only [h8059, h8356, hlam]
                              · linarith only [h8057, h8355, hlam]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            rcases p8313_3 (m.d 0 1) (by simp) with h8364 | h8364
                            · linarith only [h4610, h8364, hlam]
                            · rcases p8313_3 (m.d 0 2) (by simp) with h8366 | h8366
                              · rcases p8313_3 (m.d 0 3) (by simp) with h8367 | h8367
                                · rcases p8313_3 (m.d 0 4) (by simp) with h8368 | h8368
                                  · linarith only [h8059, h8368, hlam]
                                  · rcases p8313_3 (m.d 0 5) (by simp) with h8370 | h8370
                                    · linarith only [h8060, h8370, hlam]
                                    · rcases h2bigk with h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c | h8372c
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h0, hlam, p8372_1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8308, h8311, hc34, hlam, hphi, ht0b, ht45, ht5b, p8372_1, u0elo1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        rcases p8372_3 (m.d 0 2) (by simp) with h8376 | h8376
                                        · rcases p8372_3 (m.d 1 2) (by simp) with h8377 | h8377
                                          · rcases p8372_3 (m.d 2 3) (by simp) with h8378 | h8378
                                            · linarith only [h8056, h8378, hlam]
                                            · linarith only [h8307, h8378, hlam]
                                          · linarith only [h8302, h8377, hlam]
                                        · linarith only [h8376, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        rcases p8372_3 (m.d 0 2) (by simp) with h8383 | h8383
                                        · rcases p8372_3 (m.d 1 2) (by simp) with h8384 | h8384
                                          · rcases p8372_3 (m.d 2 3) (by simp) with h8385 | h8385
                                            · linarith only [h8056, h8385, hlam]
                                            · linarith only [h8308, h8385, hlam]
                                          · linarith only [h8303, h8384, hlam]
                                        · linarith only [h8383, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8056, h8308, h8311, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8372_1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        rcases p8372_3 (m.d 0 2) (by simp) with h8392 | h8392
                                        · linarith only [h0, h8392, hlam]
                                        · linarith only [h8056, h8392, hlam]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        rcases p8372_3 (m.d 0 2) (by simp) with h8395 | h8395
                                        · linarith only [h0, h8395, hlam]
                                        · linarith only [h8057, h8395, hlam]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        rcases p8372_3 (m.d 0 2) (by simp) with h8398 | h8398
                                        · linarith only [h0, h8398, hlam]
                                        · linarith only [h8058, h8398, hlam]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8056, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8301, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8056, h8307, hc34, hlam, hphi, ht0b, ht45, ht5b, p8372_1, u0elo1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8056, h8307, h8309, hc34, hlam, hphi, ht0b, ht45, ht5b, p8372_1, u0elo1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8057, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8302, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8307, hlam, p8372_1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8309, hlam, p8372_1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8058, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8303, hlam, p8372_0]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8308, hlam, p8372_1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [h8058, h8307, hc34, hlam, hphi, ht0b, ht45, ht5b, p8372_1, u0elo1]
                                      · have p8372_0 := h8372c.1
                                        have p8372_1 := h8372c.2.1
                                        have p8372_2 := h8372c.2.2.1
                                        have p8372_3 := h8372c.2.2.2
                                        linarith only [hlam, p8372_0]
                                · linarith only [h8060, h8367, hlam]
                              · linarith only [h8058, h8366, hlam]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8061, h8306, hc01, hc14, hlam, hphi, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8057, hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8059, hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8061, hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8061, h8306, hc01, hc14, hlam, hphi, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8058, hlam, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h8060, hlam, p8313_0]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [h6681, h8061, h8306, hc01, hc14, hlam, hphi, p8313_1]
                          · have p8313_0 := h8313c.1
                            have p8313_1 := h8313c.2.1
                            have p8313_2 := h8313c.2.2.1
                            have p8313_3 := h8313c.2.2.2
                            linarith only [hlam, p8313_0]
                    · linarith only [h8056, h8060, h8307, h8308, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8429 | h8429
                    · linarith only [h8059, h8061, h8301, h8304, h8306, h8307, h8429, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8431 | h8431
                      · linarith only [h8057, h8059, h8061, h8307, h8431, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8433 | h8433
                        · linarith only [h8059, h8061, h8433, hlam]
                        · rcases h0bigk with h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c | h8435c
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h0, hlam, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h4610, hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h6681, hlam, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h7494, hlam, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            rcases p8435_3 (m.d 0 1) (by simp) with h8441 | h8441
                            · linarith only [h0, h8441, hlam]
                            · rcases p8435_3 (m.d 0 2) (by simp) with h8443 | h8443
                              · rcases p8435_3 (m.d 0 3) (by simp) with h8444 | h8444
                                · linarith only [h8056, h8444, hlam]
                                · linarith only [h4610, h8444, hlam]
                              · linarith only [h0, h8443, hlam]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8060, h8429, hc25, hlam, hphi, ht0b, ht5b, p8435_1, u0elo1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8059, h8307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8435_1, u0elo1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8059, h8061, h8307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8435_1, u0elo1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            rcases p8435_3 (m.d 0 1) (by simp) with h8452 | h8452
                            · linarith only [h4610, h8452, hlam]
                            · rcases p8435_3 (m.d 0 2) (by simp) with h8454 | h8454
                              · rcases p8435_3 (m.d 0 3) (by simp) with h8455 | h8455
                                · rcases p8435_3 (m.d 0 4) (by simp) with h8456 | h8456
                                  · linarith only [h8059, h8456, hlam]
                                  · linarith only [h6681, h8456, hlam]
                                · linarith only [h4610, h8455, hlam]
                              · linarith only [h0, h8454, hlam]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8056, hlam, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8059, h8307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8435_1, u0elo2]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8056, h8059, h8061, h8307, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8435_1, u0elo1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8061, h8301, h8304, h8306, hc01, hc12, hlam, hphi, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8057, hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8059, hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8061, hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8061, h8301, h8304, h8306, hc01, hc12, hlam, hphi, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8058, hlam, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8060, hlam, p8435_0]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [h8059, h8061, h8301, h8304, h8306, h8307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8435_1]
                          · have p8435_0 := h8435c.1
                            have p8435_1 := h8435c.2.1
                            have p8435_2 := h8435c.2.2.1
                            have p8435_3 := h8435c.2.2.2
                            linarith only [hlam, p8435_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8475 | h8475
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8476 | h8476
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8477 | h8477
                      · linarith only [h6681, h8057, h8306, h8477, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8479 | h8479
                        · linarith only [h6681, h8306, h8475, h8479, hc01, hc24, hlam, hphi, ht12]
                        · rcases h0bigk with h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h0, hlam, p8481_1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h4610, hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h6681, hlam, p8481_1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h7494, hlam, p8481_1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8487 | h8487
                            · linarith only [h0, h8487, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8489 | h8489
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8490 | h8490
                                · linarith only [h8056, h8490, hlam]
                                · linarith only [h4610, h8490, hlam]
                              · linarith only [h0, h8489, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8056, h8476, h8479, hc34, hlam, hphi, ht0b, ht45, ht5b, p8481_1, u0elo1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8496 | h8496
                            · linarith only [h0, h8496, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8498 | h8498
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8499 | h8499
                                · linarith only [h8056, h8499, hlam]
                                · linarith only [h8059, h8499, hlam]
                              · linarith only [h8057, h8498, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8503 | h8503
                            · linarith only [h0, h8503, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8505 | h8505
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8506 | h8506
                                · linarith only [h8056, h8506, hlam]
                                · linarith only [h8060, h8506, hlam]
                              · linarith only [h8058, h8505, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8510 | h8510
                            · linarith only [h4610, h8510, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8512 | h8512
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8513 | h8513
                                · rcases p8481_3 (m.d 0 4) (by simp) with h8514 | h8514
                                  · linarith only [h8059, h8514, hlam]
                                  · linarith only [h6681, h8514, hlam]
                                · linarith only [h4610, h8513, hlam]
                              · linarith only [h0, h8512, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8056, hlam, p8481_1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8521 | h8521
                            · linarith only [h4610, h8521, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8523 | h8523
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8524 | h8524
                                · rcases p8481_3 (m.d 0 4) (by simp) with h8525 | h8525
                                  · linarith only [h8059, h8525, hlam]
                                  · rcases p8481_3 (m.d 0 5) (by simp) with h8527 | h8527
                                    · linarith only [h8060, h8527, hlam]
                                    · linarith only [h8061, h8527, hlam]
                                · linarith only [h8059, h8524, hlam]
                              · linarith only [h8057, h8523, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8532 | h8532
                            · linarith only [h4610, h8532, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8534 | h8534
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8535 | h8535
                                · rcases p8481_3 (m.d 0 4) (by simp) with h8536 | h8536
                                  · linarith only [h8059, h8536, hlam]
                                  · rcases p8481_3 (m.d 0 5) (by simp) with h8538 | h8538
                                    · linarith only [h8060, h8538, hlam]
                                    · rcases h2bigk with h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h0, hlam, p8540_1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8476, h8479, hc34, hlam, hphi, ht0b, ht45, ht5b, p8540_1, u0elo1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        rcases p8540_3 (m.d 0 2) (by simp) with h8544 | h8544
                                        · rcases p8540_3 (m.d 1 2) (by simp) with h8545 | h8545
                                          · rcases p8540_3 (m.d 2 3) (by simp) with h8546 | h8546
                                            · linarith only [h8056, h8546, hlam]
                                            · linarith only [h8475, h8546, hlam]
                                          · linarith only [h8302, h8545, hlam]
                                        · linarith only [h8544, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        rcases p8540_3 (m.d 0 2) (by simp) with h8551 | h8551
                                        · rcases p8540_3 (m.d 1 2) (by simp) with h8552 | h8552
                                          · rcases p8540_3 (m.d 2 3) (by simp) with h8553 | h8553
                                            · linarith only [h8056, h8553, hlam]
                                            · linarith only [h8476, h8553, hlam]
                                          · linarith only [h8303, h8552, hlam]
                                        · linarith only [h8551, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8056, h8061, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8481_1, p8540_1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        rcases p8540_3 (m.d 0 2) (by simp) with h8560 | h8560
                                        · linarith only [h0, h8560, hlam]
                                        · linarith only [h8056, h8560, hlam]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        rcases p8540_3 (m.d 0 2) (by simp) with h8563 | h8563
                                        · linarith only [h0, h8563, hlam]
                                        · linarith only [h8057, h8563, hlam]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        rcases p8540_3 (m.d 0 2) (by simp) with h8566 | h8566
                                        · linarith only [h0, h8566, hlam]
                                        · linarith only [h8058, h8566, hlam]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8056, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8301, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8056, hc24, hlam, hphi, ht0b, ht45, ht5b, p8540_1, u0elo1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8056, h8475, h8477, hc34, hlam, hphi, ht0b, ht45, ht5b, p8540_1, u0elo1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8057, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8302, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8475, hlam, p8540_1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8477, hlam, p8540_1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8058, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8303, hlam, p8540_0]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8476, hlam, p8540_1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [h8058, h8475, hc34, hlam, hphi, ht0b, ht45, ht5b, p8540_1, u0elo1]
                                      · have p8540_0 := h8540c.1
                                        have p8540_1 := h8540c.2.1
                                        have p8540_2 := h8540c.2.2.1
                                        have p8540_3 := h8540c.2.2.2
                                        linarith only [hlam, p8540_0]
                                · linarith only [h8060, h8535, hlam]
                              · linarith only [h8058, h8534, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h6681, h8306, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8481_1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8057, hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8059, hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8061, hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8591 | h8591
                            · linarith only [h7494, h8591, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8593 | h8593
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8594 | h8594
                                · rcases p8481_3 (m.d 0 4) (by simp) with h8595 | h8595
                                  · linarith only [h8061, h8595, hlam]
                                  · linarith only [h6681, h8595, hlam]
                                · linarith only [h4610, h8594, hlam]
                              · linarith only [h0, h8593, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8058, hlam, p8481_1]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [h8060, hlam, p8481_0]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            rcases p8481_3 (m.d 0 1) (by simp) with h8602 | h8602
                            · linarith only [h7494, h8602, hlam]
                            · rcases p8481_3 (m.d 0 2) (by simp) with h8604 | h8604
                              · rcases p8481_3 (m.d 0 3) (by simp) with h8605 | h8605
                                · rcases p8481_3 (m.d 0 4) (by simp) with h8606 | h8606
                                  · linarith only [h8061, h8606, hlam]
                                  · rcases p8481_3 (m.d 0 5) (by simp) with h8608 | h8608
                                    · rcases h2bigk with h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h0, hlam, p8609_1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8475, hc34, hlam, hphi, ht0b, ht45, ht5b, p8609_1, u0elo1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        rcases p8609_3 (m.d 0 2) (by simp) with h8613 | h8613
                                        · rcases p8609_3 (m.d 1 2) (by simp) with h8614 | h8614
                                          · rcases p8609_3 (m.d 2 3) (by simp) with h8615 | h8615
                                            · linarith only [h8056, h8615, hlam]
                                            · linarith only [h8475, h8615, hlam]
                                          · linarith only [h8302, h8614, hlam]
                                        · linarith only [h8613, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        rcases p8609_3 (m.d 0 2) (by simp) with h8620 | h8620
                                        · rcases p8609_3 (m.d 1 2) (by simp) with h8621 | h8621
                                          · rcases p8609_3 (m.d 2 3) (by simp) with h8622 | h8622
                                            · linarith only [h8056, h8622, hlam]
                                            · linarith only [h8476, h8622, hlam]
                                          · linarith only [h8303, h8621, hlam]
                                        · linarith only [h8620, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8056, h8476, h8479, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8609_1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        rcases p8609_3 (m.d 0 2) (by simp) with h8629 | h8629
                                        · linarith only [h0, h8629, hlam]
                                        · linarith only [h8056, h8629, hlam]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        rcases p8609_3 (m.d 0 2) (by simp) with h8632 | h8632
                                        · linarith only [h0, h8632, hlam]
                                        · linarith only [h8057, h8632, hlam]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        rcases p8609_3 (m.d 0 2) (by simp) with h8635 | h8635
                                        · linarith only [h0, h8635, hlam]
                                        · linarith only [h8058, h8635, hlam]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8056, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8301, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8056, hc24, hlam, hphi, ht0b, ht45, ht5b, p8609_1, u0elo1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8056, h8475, h8477, hc34, hlam, hphi, ht0b, ht45, ht5b, p8609_1, u0elo1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8057, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8302, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8475, hlam, p8609_1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8477, hlam, p8609_1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8058, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8303, hlam, p8609_0]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8476, hlam, p8609_1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [h8058, h8475, hc34, hlam, hphi, ht0b, ht45, ht5b, p8609_1, u0elo1]
                                      · have p8609_0 := h8609c.1
                                        have p8609_1 := h8609c.2.1
                                        have p8609_2 := h8609c.2.2.1
                                        have p8609_3 := h8609c.2.2.2
                                        linarith only [hlam, p8609_0]
                                    · linarith only [h8061, h8608, hlam]
                                · linarith only [h8059, h8605, hlam]
                              · linarith only [h8057, h8604, hlam]
                          · have p8481_0 := h8481c.1
                            have p8481_1 := h8481c.2.1
                            have p8481_2 := h8481c.2.2.1
                            have p8481_3 := h8481c.2.2.2
                            linarith only [hlam, p8481_0]
                    · linarith only [h8056, h8060, h8475, h8476, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8658 | h8658
                    · linarith only [h8056, h8059, h8475, h8658, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8660 | h8660
                      · linarith only [h6681, h8306, h8660, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8662 | h8662
                        · linarith only [h6681, h8059, h8306, h8662, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases h0bigk with h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h0, hlam, p8664_1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h4610, hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h6681, hlam, p8664_1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h7494, hlam, p8664_1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            rcases p8664_3 (m.d 0 1) (by simp) with h8670 | h8670
                            · linarith only [h0, h8670, hlam]
                            · rcases p8664_3 (m.d 0 2) (by simp) with h8672 | h8672
                              · rcases p8664_3 (m.d 0 3) (by simp) with h8673 | h8673
                                · linarith only [h8056, h8673, hlam]
                                · linarith only [h4610, h8673, hlam]
                              · linarith only [h0, h8672, hlam]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8059, h8475, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8664_1, u0elo1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8059, h8475, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8664_1, u0elo1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8060, h8475, h8662, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8664_1, u0elo1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            rcases p8664_3 (m.d 0 1) (by simp) with h8681 | h8681
                            · linarith only [h4610, h8681, hlam]
                            · rcases p8664_3 (m.d 0 2) (by simp) with h8683 | h8683
                              · rcases p8664_3 (m.d 0 3) (by simp) with h8684 | h8684
                                · rcases p8664_3 (m.d 0 4) (by simp) with h8685 | h8685
                                  · linarith only [h8059, h8685, hlam]
                                  · linarith only [h6681, h8685, hlam]
                                · linarith only [h4610, h8684, hlam]
                              · linarith only [h0, h8683, hlam]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8056, hlam, p8664_1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8059, h8475, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8664_1, u0elo2]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8056, h8060, h8475, h8662, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8664_1, u0elo1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h6681, h8306, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8664_1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8057, hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8059, hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8061, hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            rcases p8664_3 (m.d 0 1) (by simp) with h8699 | h8699
                            · linarith only [h7494, h8699, hlam]
                            · rcases p8664_3 (m.d 0 2) (by simp) with h8701 | h8701
                              · rcases p8664_3 (m.d 0 3) (by simp) with h8702 | h8702
                                · rcases p8664_3 (m.d 0 4) (by simp) with h8703 | h8703
                                  · linarith only [h8061, h8703, hlam]
                                  · linarith only [h6681, h8703, hlam]
                                · linarith only [h4610, h8702, hlam]
                              · linarith only [h0, h8701, hlam]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8058, hlam, p8664_1]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8060, hlam, p8664_0]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [h8059, h8475, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8664_1, u0elo4]
                          · have p8664_0 := h8664c.1
                            have p8664_1 := h8664c.2.1
                            have p8664_2 := h8664c.2.2.1
                            have p8664_3 := h8664c.2.2.2
                            linarith only [hlam, p8664_0]
              · linarith only [h4610, h8060, h8305, hlam]
            · linarith only [h4610, h8059, h8304, hlam]
          · linarith only [h0, h8058, h8303, hlam]
        · linarith only [h0, h8057, h8302, hlam]
      · linarith only [h0, h8056, h8301, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8717 | h8717
    · linarith only [h8059, h8060, h8717, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8719 | h8719
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8720 | h8720
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8721 | h8721
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8722 | h8722
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8723 | h8723
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8724 | h8724
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8725 | h8725
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8726 | h8726
                    · linarith only [h8056, h8060, h8726, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8728 | h8728
                      · linarith only [h7494, h8057, h8059, h8060, h8717, h8719, h8723, h8728, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8730 | h8730
                        · linarith only [h8056, h8060, h8717, h8719, h8723, h8725, h8730, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c | h8732c
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h0, hlam, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h4610, hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h6681, hlam, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h7494, hlam, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            rcases p8732_3 (m.d 0 1) (by simp) with h8738 | h8738
                            · linarith only [h0, h8738, hlam]
                            · rcases p8732_3 (m.d 0 2) (by simp) with h8740 | h8740
                              · rcases p8732_3 (m.d 0 3) (by simp) with h8741 | h8741
                                · linarith only [h8056, h8741, hlam]
                                · linarith only [h4610, h8741, hlam]
                              · linarith only [h0, h8740, hlam]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8056, h8725, hc34, hlam, hphi, ht0b, ht45, ht5b, p8732_1, u0elo1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            rcases p8732_3 (m.d 0 1) (by simp) with h8747 | h8747
                            · linarith only [h0, h8747, hlam]
                            · rcases p8732_3 (m.d 0 2) (by simp) with h8749 | h8749
                              · rcases p8732_3 (m.d 0 3) (by simp) with h8750 | h8750
                                · linarith only [h8056, h8750, hlam]
                                · linarith only [h8059, h8750, hlam]
                              · linarith only [h8057, h8749, hlam]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8058, h8725, h8726, hc34, hlam, hphi, ht0b, ht45, ht5b, p8732_1, u0elo1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8060, h8719, h8722, h8724, h8730, hc01, hc12, hlam, hphi, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8056, hlam, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h6681, h8060, h8719, h8722, h8724, h8730, hc01, hc12, hlam, hphi, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8060, hlam, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8059, h8060, h8719, h8722, h8724, h8730, hc01, hc12, hlam, hphi, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8057, hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8059, hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8717, hlam, p8732_0]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8060, h8719, h8722, h8724, h8730, hc01, hc12, hlam, hphi, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8058, hlam, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h8056, h8060, h8719, h8722, h8724, h8725, h8730, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [h6681, h8060, h8719, h8722, h8724, h8730, hc01, hc12, hlam, hphi, p8732_1]
                          · have p8732_0 := h8732c.1
                            have p8732_1 := h8732c.2.1
                            have p8732_2 := h8732c.2.2.1
                            have p8732_3 := h8732c.2.2.2
                            linarith only [hlam, p8732_0]
                  · linarith only [h8059, h8060, h8725, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8771 | h8771
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8772 | h8772
                    · linarith only [h8056, h8060, h8772, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8774 | h8774
                      · linarith only [h6681, h8724, h8774, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8776 | h8776
                        · linarith only [h6681, h8724, h8776, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h0, hlam, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h4610, hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h6681, hlam, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h7494, hlam, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            rcases p8778_3 (m.d 0 1) (by simp) with h8784 | h8784
                            · linarith only [h0, h8784, hlam]
                            · rcases p8778_3 (m.d 0 2) (by simp) with h8786 | h8786
                              · rcases p8778_3 (m.d 0 3) (by simp) with h8787 | h8787
                                · linarith only [h8056, h8787, hlam]
                                · linarith only [h4610, h8787, hlam]
                              · linarith only [h0, h8786, hlam]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8056, h8771, hc34, hlam, hphi, ht0b, ht45, ht5b, p8778_1, u0elo1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            rcases p8778_3 (m.d 0 1) (by simp) with h8793 | h8793
                            · linarith only [h0, h8793, hlam]
                            · rcases p8778_3 (m.d 0 2) (by simp) with h8795 | h8795
                              · rcases p8778_3 (m.d 0 3) (by simp) with h8796 | h8796
                                · linarith only [h8056, h8796, hlam]
                                · linarith only [h8059, h8796, hlam]
                              · linarith only [h8057, h8795, hlam]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8058, h8771, h8772, hc34, hlam, hphi, ht0b, ht45, ht5b, p8778_1, u0elo1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8060, h8723, hc01, hc15, hlam, hphi, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8056, hlam, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h6681, h8060, hc01, hc35, hlam, hphi, ht12, ht23, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8060, hlam, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h6681, h8724, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8057, hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8059, hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8717, hlam, p8778_0]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8060, h8719, h8723, hc01, hc12, hlam, hphi, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h8058, hlam, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h4610, h8060, h8719, h8723, hc01, hc12, hlam, hphi, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [h6681, h8060, h8719, h8723, hc01, hc12, hlam, hphi, p8778_1]
                          · have p8778_0 := h8778c.1
                            have p8778_1 := h8778c.2.1
                            have p8778_2 := h8778c.2.2.1
                            have p8778_3 := h8778c.2.2.2
                            linarith only [hlam, p8778_0]
                  · linarith only [h8059, h8060, h8719, h8723, h8771, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8817 | h8817
                · linarith only [h6681, h8717, h8722, h8723, h8817, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8819 | h8819
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8820 | h8820
                    · linarith only [h4610, h8723, h8820, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8822 | h8822
                      · linarith only [h7494, h8057, h8817, h8822, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8824 | h8824
                        · linarith only [h6681, h8817, h8824, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c | h8826c
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h0, hlam, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h4610, hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h6681, hlam, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h7494, hlam, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            rcases p8826_3 (m.d 0 1) (by simp) with h8832 | h8832
                            · linarith only [h0, h8832, hlam]
                            · rcases p8826_3 (m.d 0 2) (by simp) with h8834 | h8834
                              · rcases p8826_3 (m.d 0 3) (by simp) with h8835 | h8835
                                · linarith only [h8056, h8835, hlam]
                                · linarith only [h4610, h8835, hlam]
                              · linarith only [h0, h8834, hlam]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8056, h8819, hc34, hlam, hphi, ht0b, ht45, ht5b, p8826_1, u0elo1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            rcases p8826_3 (m.d 0 1) (by simp) with h8841 | h8841
                            · linarith only [h0, h8841, hlam]
                            · rcases p8826_3 (m.d 0 2) (by simp) with h8843 | h8843
                              · rcases p8826_3 (m.d 0 3) (by simp) with h8844 | h8844
                                · linarith only [h8056, h8844, hlam]
                                · linarith only [h8059, h8844, hlam]
                              · linarith only [h8057, h8843, hlam]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8056, h8060, h8819, hc34, hlam, hphi, ht0b, ht45, ht5b, p8826_1, u0elo1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h4610, h8723, hc01, hc35, hlam, hphi, ht12, ht23, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8056, hlam, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h4610, h8723, h8824, hc04, hc45, hlam, hphi, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8060, hlam, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h4610, h8059, h8723, h8824, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8057, hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8059, hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8717, hlam, p8826_0]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            rcases p8826_3 (m.d 0 1) (by simp) with h8859 | h8859
                            · linarith only [h7494, h8859, hlam]
                            · rcases p8826_3 (m.d 0 2) (by simp) with h8861 | h8861
                              · rcases p8826_3 (m.d 0 3) (by simp) with h8862 | h8862
                                · linarith only [h8060, h8862, hlam]
                                · linarith only [h4610, h8862, hlam]
                              · linarith only [h0, h8861, hlam]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8058, hlam, p8826_1]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [h8056, h8819, hc34, hlam, hphi, ht0b, ht45, ht5b, p8826_1, u0elo4]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            rcases p8826_3 (m.d 0 1) (by simp) with h8868 | h8868
                            · linarith only [h7494, h8868, hlam]
                            · rcases p8826_3 (m.d 0 2) (by simp) with h8870 | h8870
                              · rcases p8826_3 (m.d 0 3) (by simp) with h8871 | h8871
                                · linarith only [h8060, h8871, hlam]
                                · linarith only [h8059, h8871, hlam]
                              · linarith only [h8057, h8870, hlam]
                          · have p8826_0 := h8826c.1
                            have p8826_1 := h8826c.2.1
                            have p8826_2 := h8826c.2.2.1
                            have p8826_3 := h8826c.2.2.2
                            linarith only [hlam, p8826_0]
                  · linarith only [h4610, h8059, h8723, h8819, hc23, hc35, hlam, hphi]
            · linarith only [h4610, h8059, h8722, hlam]
          · linarith only [h0, h8058, h8721, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h8057, h8720, hlam]
      · linarith only [h0, h8056, h8719, hlam]

end R2N4
