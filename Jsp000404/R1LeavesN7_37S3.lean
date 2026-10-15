import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2158 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2159 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2160 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2161 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2162 | h2162
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2163 | h2163
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2164 | h2164
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2165 | h2165
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2166 | h2166
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2167 | h2167
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2169 | h2169
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2170 | h2170
                  · linarith only [h2158, h2170, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2172 | h2172
                    · linarith only [h2163, h2167, h2169, h2170, h2172, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2174 | h2174
                      · linarith only [h2163, h2167, h2169, h2170, h2172, h2174, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases h1bigk with h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h0, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h1650, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h1975, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2156, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          rcases p2176_3 (m.d 0 1) (by simp) with h2182 | h2182
                          · linarith only [h2182, hlam, p2176_0]
                          · rcases p2176_3 (m.d 1 2) (by simp) with h2184 | h2184
                            · rcases p2176_3 (m.d 1 3) (by simp) with h2185 | h2185
                              · linarith only [h2163, h2185, hlam]
                              · linarith only [h1650, h2185, hlam]
                            · linarith only [h2184, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2166, h2168, hc12, hlam, hphi, ht01, ht0b, ht5b, p2176_1, u5ehi1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h1975, h2162, h2169, h2170, h2174, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2176_1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2156, hc01, hc12, hlam, hphi, p2176_1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          rcases p2176_3 (m.d 0 1) (by simp) with h2193 | h2193
                          · linarith only [h2193, hlam, p2176_0]
                          · rcases p2176_3 (m.d 1 2) (by simp) with h2195 | h2195
                            · rcases p2176_3 (m.d 1 3) (by simp) with h2196 | h2196
                              · rcases p2176_3 (m.d 1 4) (by simp) with h2197 | h2197
                                · linarith only [h2166, h2197, hlam]
                                · linarith only [h1975, h2197, hlam]
                              · linarith only [h2196, hlam, p2176_0]
                            · linarith only [h0, h2195, hlam]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2163, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h1975, h2162, h2169, h2170, h2174, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2176_1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2156, h2162, h2163, h2169, h2170, h2174, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2176_1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          rcases p2176_3 (m.d 0 1) (by simp) with h2206 | h2206
                          · linarith only [h2206, hlam, p2176_0]
                          · rcases p2176_3 (m.d 1 2) (by simp) with h2208 | h2208
                            · rcases p2176_3 (m.d 1 3) (by simp) with h2209 | h2209
                              · rcases p2176_3 (m.d 1 4) (by simp) with h2210 | h2210
                                · rcases p2176_3 (m.d 1 5) (by simp) with h2211 | h2211
                                  · linarith only [h2168, h2211, hlam]
                                  · linarith only [h2156, h2211, hlam]
                                · linarith only [h2210, hlam, p2176_0]
                              · linarith only [h1650, h2209, hlam]
                            · linarith only [h0, h2208, hlam]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2164, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2166, hlam, p2176_1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2156, h2162, h2169, h2170, h2174, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2176_1]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          rcases p2176_3 (m.d 0 1) (by simp) with h2221 | h2221
                          · linarith only [h2221, hlam, p2176_0]
                          · rcases p2176_3 (m.d 1 2) (by simp) with h2223 | h2223
                            · rcases p2176_3 (m.d 1 3) (by simp) with h2224 | h2224
                              · rcases p2176_3 (m.d 1 4) (by simp) with h2225 | h2225
                                · rcases p2176_3 (m.d 1 5) (by simp) with h2226 | h2226
                                  · rcases h2bigk with h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h0, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      rcases p2227_3 (m.d 0 2) (by simp) with h2230 | h2230
                                      · rcases p2227_3 (m.d 1 2) (by simp) with h2231 | h2231
                                        · rcases p2227_3 (m.d 2 3) (by simp) with h2232 | h2232
                                          · linarith only [h2232, hlam, p2227_0]
                                          · rcases p2227_3 (m.d 2 4) (by simp) with h2234 | h2234
                                            · linarith only [h2159, h2234, hlam]
                                            · rcases p2227_3 (m.d 2 5) (by simp) with h2236 | h2236
                                              · linarith only [h2160, h2236, hlam]
                                              · linarith only [h2170, h2236, hlam]
                                        · linarith only [h2163, h2231, hlam]
                                      · linarith only [h2230, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      rcases p2227_3 (m.d 0 2) (by simp) with h2241 | h2241
                                      · rcases p2227_3 (m.d 1 2) (by simp) with h2242 | h2242
                                        · rcases p2227_3 (m.d 2 3) (by simp) with h2243 | h2243
                                          · linarith only [h2158, h2243, hlam]
                                          · linarith only [h2169, h2243, hlam]
                                        · linarith only [h2164, h2242, hlam]
                                      · linarith only [h2241, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2227_1, u5ehi2]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2158, h2169, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2227_1]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      rcases p2227_3 (m.d 0 2) (by simp) with h2251 | h2251
                                      · linarith only [h0, h2251, hlam]
                                      · linarith only [h2158, h2251, hlam]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      rcases p2227_3 (m.d 0 2) (by simp) with h2254 | h2254
                                      · linarith only [h0, h2254, hlam]
                                      · linarith only [h2159, h2254, hlam]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2227_1, u5ehi2]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2158, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2163, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2158, h2161, h2162, h2170, h2174, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2227_1]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2170, hlam, p2227_1]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2159, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2164, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2169, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2172, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2160, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h2165, hlam, p2227_0]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [h0, h2160, h2169, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2227_1]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      rcases p2227_3 (m.d 0 2) (by simp) with h2271 | h2271
                                      · rcases p2227_3 (m.d 1 2) (by simp) with h2272 | h2272
                                        · rcases p2227_3 (m.d 2 3) (by simp) with h2273 | h2273
                                          · linarith only [h2170, h2273, hlam]
                                          · linarith only [h2169, h2273, hlam]
                                        · linarith only [h2164, h2272, hlam]
                                      · linarith only [h2159, h2271, hlam]
                                    · have p2227_0 := h2227c.1
                                      have p2227_1 := h2227c.2.1
                                      have p2227_2 := h2227c.2.2.1
                                      have p2227_3 := h2227c.2.2.2
                                      linarith only [hlam, p2227_0]
                                  · linarith only [h2226, hlam, p2176_0]
                                · linarith only [h1975, h2225, hlam]
                              · linarith only [h1650, h2224, hlam]
                            · linarith only [h0, h2223, hlam]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2165, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2167, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [h2168, hlam, p2176_0]
                        · have p2176_0 := h2176c.1
                          have p2176_1 := h2176c.2.1
                          have p2176_2 := h2176c.2.2.1
                          have p2176_3 := h2176c.2.2.2
                          linarith only [hlam, p2176_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2287 | h2287
                  · linarith only [h2169, h2287, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2289 | h2289
                    · linarith only [h0, h2159, h2289, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2291 | h2291
                      · linarith only [h0, h2158, h2161, h2291, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases h1bigk with h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h0, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h1650, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h1975, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2156, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          rcases p2293_3 (m.d 0 1) (by simp) with h2299 | h2299
                          · linarith only [h2299, hlam, p2293_0]
                          · rcases p2293_3 (m.d 1 2) (by simp) with h2301 | h2301
                            · rcases p2293_3 (m.d 1 3) (by simp) with h2302 | h2302
                              · linarith only [h2163, h2302, hlam]
                              · linarith only [h1650, h2302, hlam]
                            · linarith only [h2301, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h1650, hc01, hc12, hlam, hphi, p2293_1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h1975, h2162, h2169, h2291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2293_1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2293_1, u5ehi1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          rcases p2293_3 (m.d 0 1) (by simp) with h2310 | h2310
                          · linarith only [h2310, hlam, p2293_0]
                          · rcases p2293_3 (m.d 1 2) (by simp) with h2312 | h2312
                            · rcases p2293_3 (m.d 1 3) (by simp) with h2313 | h2313
                              · rcases p2293_3 (m.d 1 4) (by simp) with h2314 | h2314
                                · linarith only [h2166, h2314, hlam]
                                · linarith only [h1975, h2314, hlam]
                              · linarith only [h2313, hlam, p2293_0]
                            · linarith only [h0, h2312, hlam]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2163, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h1975, h2162, h2169, h2291, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2293_1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2156, h2162, h2163, h2169, h2291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2293_1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          rcases p2293_3 (m.d 0 1) (by simp) with h2323 | h2323
                          · linarith only [h2323, hlam, p2293_0]
                          · rcases p2293_3 (m.d 1 2) (by simp) with h2325 | h2325
                            · rcases p2293_3 (m.d 1 3) (by simp) with h2326 | h2326
                              · rcases p2293_3 (m.d 1 4) (by simp) with h2327 | h2327
                                · rcases p2293_3 (m.d 1 5) (by simp) with h2328 | h2328
                                  · linarith only [h2168, h2328, hlam]
                                  · linarith only [h2156, h2328, hlam]
                                · linarith only [h2327, hlam, p2293_0]
                              · linarith only [h1650, h2326, hlam]
                            · linarith only [h0, h2325, hlam]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2164, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2166, hlam, p2293_1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2156, h2162, h2169, h2291, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2293_1]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          rcases p2293_3 (m.d 0 1) (by simp) with h2338 | h2338
                          · linarith only [h2338, hlam, p2293_0]
                          · rcases p2293_3 (m.d 1 2) (by simp) with h2340 | h2340
                            · rcases p2293_3 (m.d 1 3) (by simp) with h2341 | h2341
                              · rcases p2293_3 (m.d 1 4) (by simp) with h2342 | h2342
                                · rcases p2293_3 (m.d 1 5) (by simp) with h2343 | h2343
                                  · rcases h2bigk with h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h0, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2158, h2161, h2162, h2169, h2291, hlam, p2344_2]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      rcases p2344_3 (m.d 0 2) (by simp) with h2348 | h2348
                                      · rcases p2344_3 (m.d 1 2) (by simp) with h2349 | h2349
                                        · rcases p2344_3 (m.d 2 3) (by simp) with h2350 | h2350
                                          · linarith only [h2158, h2350, hlam]
                                          · rcases p2344_3 (m.d 2 4) (by simp) with h2352 | h2352
                                            · linarith only [h2352, hlam, p2344_0]
                                            · rcases p2344_3 (m.d 2 5) (by simp) with h2354 | h2354
                                              · linarith only [h2160, h2354, hlam]
                                              · linarith only [h2289, h2354, hlam]
                                        · linarith only [h2164, h2349, hlam]
                                      · linarith only [h2348, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht0b, ht5b, p2344_1, u5ehi2]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2158, h2161, h2162, h2169, h2291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2344_1]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h0, h2158, h2161, h2162, h2169, h2291, hlam, p2344_2]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      rcases p2344_3 (m.d 0 2) (by simp) with h2363 | h2363
                                      · linarith only [h0, h2363, hlam]
                                      · linarith only [h2159, h2363, hlam]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2344_1, u5ehi2]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2158, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2163, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2169, hlam, p2344_1]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2287, hlam, p2344_1]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2159, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2164, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2158, h2161, h2162, h2169, h2291, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2344_1]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2289, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2160, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [h2165, hlam, p2344_0]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      rcases p2344_3 (m.d 0 2) (by simp) with h2379 | h2379
                                      · rcases p2344_3 (m.d 1 2) (by simp) with h2380 | h2380
                                        · rcases p2344_3 (m.d 2 3) (by simp) with h2381 | h2381
                                          · linarith only [h2287, h2381, hlam]
                                          · rcases p2344_3 (m.d 2 4) (by simp) with h2383 | h2383
                                            · linarith only [h2289, h2383, hlam]
                                            · linarith only [h2169, h2383, hlam]
                                        · linarith only [h2163, h2380, hlam]
                                      · linarith only [h2158, h2379, hlam]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      rcases p2344_3 (m.d 0 2) (by simp) with h2388 | h2388
                                      · rcases p2344_3 (m.d 1 2) (by simp) with h2389 | h2389
                                        · rcases p2344_3 (m.d 2 3) (by simp) with h2390 | h2390
                                          · linarith only [h2287, h2390, hlam]
                                          · rcases p2344_3 (m.d 2 4) (by simp) with h2392 | h2392
                                            · linarith only [h2289, h2392, hlam]
                                            · rcases p2344_3 (m.d 2 5) (by simp) with h2394 | h2394
                                              · rcases h4bigk with h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h1975, hlam, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2162, h2289, hlam, p2344_1, p2395_2]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  rcases p2395_3 (m.d 0 4) (by simp) with h2399 | h2399
                                                  · rcases p2395_3 (m.d 1 4) (by simp) with h2400 | h2400
                                                    · rcases p2395_3 (m.d 2 4) (by simp) with h2401 | h2401
                                                      · linarith only [h2159, h2401, hlam]
                                                      · rcases p2395_3 (m.d 3 4) (by simp) with h2403 | h2403
                                                        · linarith only [h2161, h2403, hlam]
                                                        · rcases p2395_3 (m.d 4 5) (by simp) with h2405 | h2405
                                                          · linarith only [h2162, h2405, hlam]
                                                          · linarith only [h2291, h2405, hlam]
                                                    · linarith only [h2166, h2400, hlam]
                                                  · linarith only [h2161, h2399, hlam]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h0, h2158, h2161, h2287, h2291, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2344_1, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2162, h2163, h2166, h2287, h2291, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2344_1, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h1975, h2162, h2287, h2291, hlam, p2344_1, p2395_2]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  rcases p2395_3 (m.d 0 4) (by simp) with h2414 | h2414
                                                  · linarith only [h1975, h2414, hlam]
                                                  · linarith only [h2161, h2414, hlam]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2169, h2287, h2291, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2344_1, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2159, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2164, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2169, hlam, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2289, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2161, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2166, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2162, h2169, h2291, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2291, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2162, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h2168, hlam, p2395_0]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  rcases p2395_3 (m.d 0 4) (by simp) with h2430 | h2430
                                                  · rcases p2395_3 (m.d 1 4) (by simp) with h2431 | h2431
                                                    · rcases p2395_3 (m.d 2 4) (by simp) with h2432 | h2432
                                                      · linarith only [h2432, hlam, p2395_0]
                                                      · rcases p2395_3 (m.d 3 4) (by simp) with h2434 | h2434
                                                        · linarith only [h2291, h2434, hlam]
                                                        · linarith only [h2169, h2434, hlam]
                                                    · linarith only [h2164, h2431, hlam]
                                                  · linarith only [h2159, h2430, hlam]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [h1975, h2162, h2163, h2166, h2169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2395_1]
                                                · have p2395_0 := h2395c.1
                                                  have p2395_1 := h2395c.2.1
                                                  have p2395_2 := h2395c.2.2.1
                                                  have p2395_3 := h2395c.2.2.2
                                                  linarith only [hlam, p2395_0]
                                              · linarith only [h2289, h2394, hlam]
                                        · linarith only [h2164, h2389, hlam]
                                      · linarith only [h2159, h2388, hlam]
                                    · have p2344_0 := h2344c.1
                                      have p2344_1 := h2344c.2.1
                                      have p2344_2 := h2344c.2.2.1
                                      have p2344_3 := h2344c.2.2.2
                                      linarith only [hlam, p2344_0]
                                  · linarith only [h2343, hlam, p2293_0]
                                · linarith only [h1975, h2342, hlam]
                              · linarith only [h1650, h2341, hlam]
                            · linarith only [h0, h2340, hlam]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2165, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2167, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [h2168, hlam, p2293_0]
                        · have p2293_0 := h2293c.1
                          have p2293_1 := h2293c.2.1
                          have p2293_2 := h2293c.2.2.1
                          have p2293_3 := h2293c.2.2.2
                          linarith only [hlam, p2293_0]
              · linarith only [h1975, h2162, h2168, hlam]
            · linarith only [h1975, h2162, h2166, h2167, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · linarith only [h1650, h2161, h2166, hlam]
        · linarith only [h0, h2158, h2161, h2162, h2165, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · linarith only [h0, h2158, h2161, h2162, h2164, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
    · linarith only [h0, h2158, h2161, h2162, h2163, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2459 | h2459
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2460 | h2460
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2461 | h2461
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2462 | h2462
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2463 | h2463
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2464 | h2464
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2465 | h2465
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2466 | h2466
                  · linarith only [h2158, h2466, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2468 | h2468
                    · linarith only [h2159, h2162, h2468, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2470 | h2470
                      · linarith only [h2162, h2459, h2463, h2465, h2466, h2470, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h0, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h1650, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h1975, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2156, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          rcases p2472_3 (m.d 0 1) (by simp) with h2478 | h2478
                          · linarith only [h2478, hlam, p2472_0]
                          · rcases p2472_3 (m.d 1 2) (by simp) with h2480 | h2480
                            · rcases p2472_3 (m.d 1 3) (by simp) with h2481 | h2481
                              · linarith only [h2459, h2481, hlam]
                              · linarith only [h1650, h2481, hlam]
                            · linarith only [h2480, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2462, h2464, hc12, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi1]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2160, h2162, h2464, hc12, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi2]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2156, h2160, hc12, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi2]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          rcases p2472_3 (m.d 0 1) (by simp) with h2489 | h2489
                          · linarith only [h2489, hlam, p2472_0]
                          · rcases p2472_3 (m.d 1 2) (by simp) with h2491 | h2491
                            · rcases p2472_3 (m.d 1 3) (by simp) with h2492 | h2492
                              · rcases p2472_3 (m.d 1 4) (by simp) with h2493 | h2493
                                · linarith only [h2462, h2493, hlam]
                                · linarith only [h1975, h2493, hlam]
                              · linarith only [h2492, hlam, p2472_0]
                            · linarith only [h0, h2491, hlam]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2459, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2160, h2162, h2464, hc13, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi2]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2160, h2162, h2459, h2464, hc12, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi2]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          rcases p2472_3 (m.d 0 1) (by simp) with h2502 | h2502
                          · linarith only [h2502, hlam, p2472_0]
                          · rcases p2472_3 (m.d 1 2) (by simp) with h2504 | h2504
                            · rcases p2472_3 (m.d 1 3) (by simp) with h2505 | h2505
                              · rcases p2472_3 (m.d 1 4) (by simp) with h2506 | h2506
                                · rcases p2472_3 (m.d 1 5) (by simp) with h2507 | h2507
                                  · linarith only [h2464, h2507, hlam]
                                  · linarith only [h2156, h2507, hlam]
                                · linarith only [h2506, hlam, p2472_0]
                              · linarith only [h1650, h2505, hlam]
                            · linarith only [h0, h2504, hlam]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2460, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2462, hlam, p2472_1]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2160, h2162, h2464, hc14, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi2]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          rcases p2472_3 (m.d 0 1) (by simp) with h2517 | h2517
                          · linarith only [h2517, hlam, p2472_0]
                          · rcases p2472_3 (m.d 1 2) (by simp) with h2519 | h2519
                            · rcases p2472_3 (m.d 1 3) (by simp) with h2520 | h2520
                              · rcases p2472_3 (m.d 1 4) (by simp) with h2521 | h2521
                                · rcases p2472_3 (m.d 1 5) (by simp) with h2522 | h2522
                                  · rcases h2bigk with h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h0, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      rcases p2523_3 (m.d 0 2) (by simp) with h2526 | h2526
                                      · rcases p2523_3 (m.d 1 2) (by simp) with h2527 | h2527
                                        · rcases p2523_3 (m.d 2 3) (by simp) with h2528 | h2528
                                          · linarith only [h2528, hlam, p2523_0]
                                          · rcases p2523_3 (m.d 2 4) (by simp) with h2530 | h2530
                                            · linarith only [h2159, h2530, hlam]
                                            · rcases p2523_3 (m.d 2 5) (by simp) with h2532 | h2532
                                              · linarith only [h2160, h2532, hlam]
                                              · linarith only [h2466, h2532, hlam]
                                        · linarith only [h2459, h2527, hlam]
                                      · linarith only [h2526, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      rcases p2523_3 (m.d 0 2) (by simp) with h2537 | h2537
                                      · rcases p2523_3 (m.d 1 2) (by simp) with h2538 | h2538
                                        · rcases p2523_3 (m.d 2 3) (by simp) with h2539 | h2539
                                          · linarith only [h2158, h2539, hlam]
                                          · linarith only [h2465, h2539, hlam]
                                        · linarith only [h2460, h2538, hlam]
                                      · linarith only [h2537, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2523_1, u5ehi2]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2158, h2465, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2523_1]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      rcases p2523_3 (m.d 0 2) (by simp) with h2547 | h2547
                                      · linarith only [h0, h2547, hlam]
                                      · linarith only [h2158, h2547, hlam]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      rcases p2523_3 (m.d 0 2) (by simp) with h2550 | h2550
                                      · linarith only [h0, h2550, hlam]
                                      · linarith only [h2159, h2550, hlam]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2523_1, u5ehi2]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2158, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2459, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2459, h2463, h2466, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2523_1]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2466, hlam, p2523_1]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2159, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2460, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2465, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2468, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2160, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2461, hlam, p2523_0]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [h2160, h2465, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2523_1]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      rcases p2523_3 (m.d 0 2) (by simp) with h2567 | h2567
                                      · rcases p2523_3 (m.d 1 2) (by simp) with h2568 | h2568
                                        · rcases p2523_3 (m.d 2 3) (by simp) with h2569 | h2569
                                          · linarith only [h2466, h2569, hlam]
                                          · linarith only [h2465, h2569, hlam]
                                        · linarith only [h2460, h2568, hlam]
                                      · linarith only [h2159, h2567, hlam]
                                    · have p2523_0 := h2523c.1
                                      have p2523_1 := h2523c.2.1
                                      have p2523_2 := h2523c.2.2.1
                                      have p2523_3 := h2523c.2.2.2
                                      linarith only [hlam, p2523_0]
                                  · linarith only [h2522, hlam, p2472_0]
                                · linarith only [h1975, h2521, hlam]
                              · linarith only [h1650, h2520, hlam]
                            · linarith only [h0, h2519, hlam]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2461, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2463, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [h2464, hlam, p2472_0]
                        · have p2472_0 := h2472c.1
                          have p2472_1 := h2472c.2.1
                          have p2472_2 := h2472c.2.2.1
                          have p2472_3 := h2472c.2.2.2
                          linarith only [hlam, p2472_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2583 | h2583
                  · linarith only [h2161, h2162, h2459, h2462, h2464, h2465, h2583, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2585 | h2585
                    · linarith only [h0, h2159, h2162, h2585, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2587 | h2587
                      · linarith only [h2161, h2162, h2587, hlam]
                      · rcases h1bigk with h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h0, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h1650, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h1975, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2156, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          rcases p2589_3 (m.d 0 1) (by simp) with h2595 | h2595
                          · linarith only [h2595, hlam, p2589_0]
                          · rcases p2589_3 (m.d 1 2) (by simp) with h2597 | h2597
                            · rcases p2589_3 (m.d 1 3) (by simp) with h2598 | h2598
                              · linarith only [h2459, h2598, hlam]
                              · linarith only [h1650, h2598, hlam]
                            · linarith only [h2597, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h1650, hc01, hc12, hlam, hphi, p2589_1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h1975, hc01, hc12, hlam, hphi, p2589_1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2589_1, u5ehi1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          rcases p2589_3 (m.d 0 1) (by simp) with h2606 | h2606
                          · linarith only [h2606, hlam, p2589_0]
                          · rcases p2589_3 (m.d 1 2) (by simp) with h2608 | h2608
                            · rcases p2589_3 (m.d 1 3) (by simp) with h2609 | h2609
                              · rcases p2589_3 (m.d 1 4) (by simp) with h2610 | h2610
                                · linarith only [h2462, h2610, hlam]
                                · linarith only [h1975, h2610, hlam]
                              · linarith only [h2609, hlam, p2589_0]
                            · linarith only [h0, h2608, hlam]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2459, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2161, h2162, h2464, h2465, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2589_1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2161, h2162, h2459, h2464, h2465, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2589_1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          rcases p2589_3 (m.d 0 1) (by simp) with h2619 | h2619
                          · linarith only [h2619, hlam, p2589_0]
                          · rcases p2589_3 (m.d 1 2) (by simp) with h2621 | h2621
                            · rcases p2589_3 (m.d 1 3) (by simp) with h2622 | h2622
                              · rcases p2589_3 (m.d 1 4) (by simp) with h2623 | h2623
                                · rcases p2589_3 (m.d 1 5) (by simp) with h2624 | h2624
                                  · linarith only [h2464, h2624, hlam]
                                  · linarith only [h2156, h2624, hlam]
                                · linarith only [h2623, hlam, p2589_0]
                              · linarith only [h1650, h2622, hlam]
                            · linarith only [h0, h2621, hlam]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2460, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2462, hlam, p2589_1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2161, h2162, h2464, h2465, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2589_1]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          rcases p2589_3 (m.d 0 1) (by simp) with h2634 | h2634
                          · linarith only [h2634, hlam, p2589_0]
                          · rcases p2589_3 (m.d 1 2) (by simp) with h2636 | h2636
                            · rcases p2589_3 (m.d 1 3) (by simp) with h2637 | h2637
                              · rcases p2589_3 (m.d 1 4) (by simp) with h2638 | h2638
                                · rcases p2589_3 (m.d 1 5) (by simp) with h2639 | h2639
                                  · rcases h2bigk with h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c | h2640c
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h0, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      rcases p2640_3 (m.d 0 2) (by simp) with h2643 | h2643
                                      · rcases p2640_3 (m.d 1 2) (by simp) with h2644 | h2644
                                        · rcases p2640_3 (m.d 2 3) (by simp) with h2645 | h2645
                                          · linarith only [h2645, hlam, p2640_0]
                                          · rcases p2640_3 (m.d 2 4) (by simp) with h2647 | h2647
                                            · linarith only [h2159, h2647, hlam]
                                            · linarith only [h2465, h2647, hlam]
                                        · linarith only [h2459, h2644, hlam]
                                      · linarith only [h2643, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      rcases p2640_3 (m.d 0 2) (by simp) with h2652 | h2652
                                      · rcases p2640_3 (m.d 1 2) (by simp) with h2653 | h2653
                                        · rcases p2640_3 (m.d 2 3) (by simp) with h2654 | h2654
                                          · linarith only [h2158, h2654, hlam]
                                          · rcases p2640_3 (m.d 2 4) (by simp) with h2656 | h2656
                                            · linarith only [h2656, hlam, p2640_0]
                                            · rcases p2640_3 (m.d 2 5) (by simp) with h2658 | h2658
                                              · linarith only [h2160, h2658, hlam]
                                              · linarith only [h2585, h2658, hlam]
                                        · linarith only [h2460, h2653, hlam]
                                      · linarith only [h2652, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht0b, ht5b, p2640_1, u5ehi2]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2158, h2161, h2465, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2640_1]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2161, h2162, h2459, h2462, h2464, h2465, hlam, p2640_2]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      rcases p2640_3 (m.d 0 2) (by simp) with h2667 | h2667
                                      · linarith only [h0, h2667, hlam]
                                      · linarith only [h2159, h2667, hlam]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2640_1, u5ehi2]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2158, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2459, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2465, hlam, p2640_1]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2583, hlam, p2640_1]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2159, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2460, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2161, h2162, h2462, h2464, h2465, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2640_1]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2585, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2160, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [h2461, hlam, p2640_0]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      rcases p2640_3 (m.d 0 2) (by simp) with h2683 | h2683
                                      · rcases p2640_3 (m.d 1 2) (by simp) with h2684 | h2684
                                        · rcases p2640_3 (m.d 2 3) (by simp) with h2685 | h2685
                                          · linarith only [h2583, h2685, hlam]
                                          · rcases p2640_3 (m.d 2 4) (by simp) with h2687 | h2687
                                            · linarith only [h2585, h2687, hlam]
                                            · linarith only [h2465, h2687, hlam]
                                        · linarith only [h2459, h2684, hlam]
                                      · linarith only [h2158, h2683, hlam]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      rcases p2640_3 (m.d 0 2) (by simp) with h2692 | h2692
                                      · rcases p2640_3 (m.d 1 2) (by simp) with h2693 | h2693
                                        · rcases p2640_3 (m.d 2 3) (by simp) with h2694 | h2694
                                          · linarith only [h2583, h2694, hlam]
                                          · rcases p2640_3 (m.d 2 4) (by simp) with h2696 | h2696
                                            · linarith only [h2585, h2696, hlam]
                                            · rcases p2640_3 (m.d 2 5) (by simp) with h2698 | h2698
                                              · rcases h4bigk with h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h1975, hlam, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2162, h2459, h2462, h2464, h2465, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2162, h2459, h2462, h2464, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2162, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  rcases p2699_3 (m.d 0 4) (by simp) with h2705 | h2705
                                                  · linarith only [h1975, h2705, hlam]
                                                  · rcases p2699_3 (m.d 1 4) (by simp) with h2707 | h2707
                                                    · rcases p2699_3 (m.d 2 4) (by simp) with h2708 | h2708
                                                      · linarith only [h2460, h2708, hlam]
                                                      · rcases p2699_3 (m.d 3 4) (by simp) with h2710 | h2710
                                                        · linarith only [h2462, h2710, hlam]
                                                        · rcases p2699_3 (m.d 4 5) (by simp) with h2712 | h2712
                                                          · linarith only [h2464, h2712, hlam]
                                                          · linarith only [h2162, h2712, hlam]
                                                    · linarith only [h1975, h2707, hlam]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2160, h2162, h2464, hlam, p2640_1, p2699_2]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  rcases p2699_3 (m.d 0 4) (by simp) with h2718 | h2718
                                                  · linarith only [h1975, h2718, hlam]
                                                  · linarith only [h2161, h2718, hlam]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2162, h2459, h2462, hc12, hlam, hphi, ht01, ht0b, ht5b, p2699_1, u5ehi0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2159, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2460, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2465, hlam, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2585, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2161, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2462, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2161, h2162, hc24, hc45, hlam, hphi, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2587, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h1975, h2459, h2462, h2464, hc01, hc12, hlam, hphi, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2464, hlam, p2699_0]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  rcases p2699_3 (m.d 0 4) (by simp) with h2734 | h2734
                                                  · linarith only [h2162, h2734, hlam]
                                                  · linarith only [h2159, h2734, hlam]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [h2459, h2462, h2464, h2465, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2699_1]
                                                · have p2699_0 := h2699c.1
                                                  have p2699_1 := h2699c.2.1
                                                  have p2699_2 := h2699c.2.2.1
                                                  have p2699_3 := h2699c.2.2.2
                                                  linarith only [hlam, p2699_0]
                                              · linarith only [h2585, h2698, hlam]
                                        · linarith only [h2460, h2693, hlam]
                                      · linarith only [h2159, h2692, hlam]
                                    · have p2640_0 := h2640c.1
                                      have p2640_1 := h2640c.2.1
                                      have p2640_2 := h2640c.2.2.1
                                      have p2640_3 := h2640c.2.2.2
                                      linarith only [hlam, p2640_0]
                                  · linarith only [h2639, hlam, p2589_0]
                                · linarith only [h1975, h2638, hlam]
                              · linarith only [h1650, h2637, hlam]
                            · linarith only [h0, h2636, hlam]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2461, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2463, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [h2464, hlam, p2589_0]
                        · have p2589_0 := h2589c.1
                          have p2589_1 := h2589c.2.1
                          have p2589_2 := h2589c.2.2.1
                          have p2589_3 := h2589c.2.2.2
                          linarith only [hlam, p2589_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2751 | h2751
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2752 | h2752
                  · linarith only [h2158, h2752, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2754 | h2754
                    · linarith only [h0, h2159, h2754, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2756 | h2756
                      · linarith only [h1975, h2459, h2463, h2464, h2751, h2752, h2756, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h0, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h1650, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h1975, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2156, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          rcases p2758_3 (m.d 0 1) (by simp) with h2764 | h2764
                          · linarith only [h2764, hlam, p2758_0]
                          · rcases p2758_3 (m.d 1 2) (by simp) with h2766 | h2766
                            · rcases p2758_3 (m.d 1 3) (by simp) with h2767 | h2767
                              · linarith only [h2459, h2767, hlam]
                              · linarith only [h1650, h2767, hlam]
                            · linarith only [h2766, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2463, h2752, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h1975, hc01, hc12, hlam, hphi, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2758_1, u5ehi1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          rcases p2758_3 (m.d 0 1) (by simp) with h2775 | h2775
                          · linarith only [h2775, hlam, p2758_0]
                          · rcases p2758_3 (m.d 1 2) (by simp) with h2777 | h2777
                            · rcases p2758_3 (m.d 1 3) (by simp) with h2778 | h2778
                              · rcases p2758_3 (m.d 1 4) (by simp) with h2779 | h2779
                                · linarith only [h2462, h2779, hlam]
                                · linarith only [h1975, h2779, hlam]
                              · linarith only [h2778, hlam, p2758_0]
                            · linarith only [h0, h2777, hlam]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2459, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h1975, hc01, hc13, hlam, hphi, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2156, h2160, h2459, hc12, hlam, hphi, ht01, ht0b, ht5b, p2758_1, u5ehi2]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2464, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2460, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2462, hlam, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2464, hlam, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          rcases p2758_3 (m.d 0 1) (by simp) with h2793 | h2793
                          · linarith only [h2793, hlam, p2758_0]
                          · rcases p2758_3 (m.d 1 2) (by simp) with h2795 | h2795
                            · rcases p2758_3 (m.d 1 3) (by simp) with h2796 | h2796
                              · rcases p2758_3 (m.d 1 4) (by simp) with h2797 | h2797
                                · linarith only [h2464, h2797, hlam]
                                · linarith only [h1975, h2797, hlam]
                              · linarith only [h1650, h2796, hlam]
                            · linarith only [h0, h2795, hlam]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2461, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h2463, hlam, p2758_0]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [h1975, hc01, hc15, hlam, hphi, p2758_1]
                        · have p2758_0 := h2758c.1
                          have p2758_1 := h2758c.2.1
                          have p2758_2 := h2758c.2.2.1
                          have p2758_3 := h2758c.2.2.2
                          linarith only [hlam, p2758_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2806 | h2806
                  · linarith only [h2161, h2751, h2806, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2808 | h2808
                    · linarith only [h1975, h2161, h2464, h2751, h2808, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2810 | h2810
                      · linarith only [h1975, h2161, h2464, h2810, hlam]
                      · rcases h1bigk with h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h0, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h1650, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h1975, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2156, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          rcases p2812_3 (m.d 0 1) (by simp) with h2818 | h2818
                          · linarith only [h2818, hlam, p2812_0]
                          · rcases p2812_3 (m.d 1 2) (by simp) with h2820 | h2820
                            · rcases p2812_3 (m.d 1 3) (by simp) with h2821 | h2821
                              · linarith only [h2459, h2821, hlam]
                              · linarith only [h1650, h2821, hlam]
                            · linarith only [h2820, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h1650, hc01, hc12, hlam, hphi, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h1975, hc01, hc12, hlam, hphi, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2812_1, u5ehi1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          rcases p2812_3 (m.d 0 1) (by simp) with h2829 | h2829
                          · linarith only [h2829, hlam, p2812_0]
                          · rcases p2812_3 (m.d 1 2) (by simp) with h2831 | h2831
                            · rcases p2812_3 (m.d 1 3) (by simp) with h2832 | h2832
                              · rcases p2812_3 (m.d 1 4) (by simp) with h2833 | h2833
                                · linarith only [h2462, h2833, hlam]
                                · linarith only [h1975, h2833, hlam]
                              · linarith only [h2832, hlam, p2812_0]
                            · linarith only [h0, h2831, hlam]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2459, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h1975, hc01, hc13, hlam, hphi, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2156, h2160, h2459, hc12, hlam, hphi, ht01, ht0b, ht5b, p2812_1, u5ehi2]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2464, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2460, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2462, hlam, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2464, hlam, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          rcases p2812_3 (m.d 0 1) (by simp) with h2847 | h2847
                          · linarith only [h2847, hlam, p2812_0]
                          · rcases p2812_3 (m.d 1 2) (by simp) with h2849 | h2849
                            · rcases p2812_3 (m.d 1 3) (by simp) with h2850 | h2850
                              · rcases p2812_3 (m.d 1 4) (by simp) with h2851 | h2851
                                · linarith only [h2464, h2851, hlam]
                                · linarith only [h1975, h2851, hlam]
                              · linarith only [h1650, h2850, hlam]
                            · linarith only [h0, h2849, hlam]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2461, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h2463, hlam, p2812_0]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [h1975, hc01, hc15, hlam, hphi, p2812_1]
                        · have p2812_0 := h2812c.1
                          have p2812_1 := h2812c.2.1
                          have p2812_2 := h2812c.2.2.1
                          have p2812_3 := h2812c.2.2.2
                          linarith only [hlam, p2812_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2860 | h2860
              · linarith only [h2462, h2463, h2860, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2862 | h2862
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2863 | h2863
                  · linarith only [h1650, h2463, h2863, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2865 | h2865
                    · linarith only [h0, h2156, h2159, h2160, h2860, h2865, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2867 | h2867
                      · linarith only [h1650, h1975, h2158, h2463, h2860, h2862, h2867, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases h1bigk with h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h0, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1650, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1975, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2156, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          rcases p2869_3 (m.d 0 1) (by simp) with h2875 | h2875
                          · linarith only [h2875, hlam, p2869_0]
                          · rcases p2869_3 (m.d 1 2) (by simp) with h2877 | h2877
                            · rcases p2869_3 (m.d 1 3) (by simp) with h2878 | h2878
                              · linarith only [h2459, h2878, hlam]
                              · linarith only [h1650, h2878, hlam]
                            · linarith only [h2877, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1650, hc01, hc12, hlam, hphi, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1975, hc01, hc12, hlam, hphi, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2156, h2160, hc12, hlam, hphi, ht01, ht0b, ht5b, p2869_1, u5ehi2]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2463, hc01, hc35, hlam, hphi, ht12, ht23, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2459, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1975, h2463, h2867, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2463, hlam, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2462, h2463, h2867, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2460, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2462, hlam, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2860, hlam, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          rcases p2869_3 (m.d 0 1) (by simp) with h2896 | h2896
                          · linarith only [h2896, hlam, p2869_0]
                          · rcases p2869_3 (m.d 1 2) (by simp) with h2898 | h2898
                            · rcases p2869_3 (m.d 1 3) (by simp) with h2899 | h2899
                              · linarith only [h2463, h2899, hlam]
                              · linarith only [h1650, h2899, hlam]
                            · linarith only [h0, h2898, hlam]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h2461, hlam, p2869_0]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1650, hc01, hc15, hlam, hphi, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [h1975, hc01, hc15, hlam, hphi, p2869_1]
                        · have p2869_0 := h2869c.1
                          have p2869_1 := h2869c.2.1
                          have p2869_2 := h2869c.2.2.1
                          have p2869_3 := h2869c.2.2.2
                          linarith only [hlam, p2869_0]
                · linarith only [h1650, h2161, h2463, h2862, hc23, hc35, hlam, hphi]
          · linarith only [h1650, h2161, h2462, hlam]
        · linarith only [h0, h2160, h2461, hlam]
      · linarith only [h0, h2159, h2160, h2460, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
    · linarith only [h0, h2160, h2459, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]

end R2N4
