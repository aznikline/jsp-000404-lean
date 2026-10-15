import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2063 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h2142 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h2143 | h2143
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2144 | h2144
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2145 | h2145
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2146 | h2146
        · linarith only [h1, h2146, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2148 | h2148
          · linarith only [h1, h2063, h2148, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2151 | h2151
              · linarith only [h0, h2, h2150, h2151, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2153 | h2153
                · linarith only [h1, h2063, h2143, h2153, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2155 | h2155
                  · linarith only [h0, h2144, h2155, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2157 | h2157
                    · rcases h0bigk with h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c | h2158c
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h0, h2144, h2150, h2151, h2155, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        rcases p2158_3 (m.d 0 1) (by simp) with h2161 | h2161
                        · rcases p2158_3 (m.d 0 2) (by simp) with h2162 | h2162
                          · linarith only [h0, h2162, hlam]
                          · linarith only [h2162, h4, hlam]
                        · linarith only [h1, h2161, hlam]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h2142, h2151, h2155, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        rcases p2158_3 (m.d 0 1) (by simp) with h2167 | h2167
                        · rcases p2158_3 (m.d 0 2) (by simp) with h2168 | h2168
                          · linarith only [h0, h2168, hlam]
                          · linarith only [h2168, h6, hlam]
                        · linarith only [h2167, h3, hlam]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h0, hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        rcases p2158_3 (m.d 0 1) (by simp) with h2174 | h2174
                        · rcases p2158_3 (m.d 0 2) (by simp) with h2175 | h2175
                          · rcases p2158_3 (m.d 0 3) (by simp) with h2176 | h2176
                            · linarith only [h2176, h4, hlam]
                            · rcases p2158_3 (m.d 0 4) (by simp) with h2178 | h2178
                              · linarith only [h2178, h5, hlam]
                              · linarith only [h2178, h7, hlam]
                          · linarith only [h2175, h4, hlam]
                        · linarith only [h1, h2174, hlam]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h2, h2150, h2151, h2155, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        rcases p2158_3 (m.d 0 1) (by simp) with h2184 | h2184
                        · rcases p2158_3 (m.d 0 2) (by simp) with h2185 | h2185
                          · rcases p2158_3 (m.d 0 3) (by simp) with h2186 | h2186
                            · linarith only [h2186, h4, hlam]
                            · rcases p2158_3 (m.d 0 4) (by simp) with h2188 | h2188
                              · linarith only [h2188, h5, hlam]
                              · linarith only [h2142, h2188, hlam]
                          · linarith only [h2185, h6, hlam]
                        · linarith only [h2184, h3, hlam]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h1, hlam, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h4, hlam, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h7, hlam, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h2063, hlam, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h2, hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h5, hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        rcases p2158_3 (m.d 0 1) (by simp) with h2200 | h2200
                        · rcases p2158_3 (m.d 0 2) (by simp) with h2201 | h2201
                          · rcases p2158_3 (m.d 0 3) (by simp) with h2202 | h2202
                            · linarith only [h2202, h7, hlam]
                            · rcases p2158_3 (m.d 0 4) (by simp) with h2204 | h2204
                              · rcases p2158_3 (m.d 0 5) (by simp) with h2205 | h2205
                                · linarith only [h2142, h2205, hlam]
                                · linarith only [h2063, h2205, hlam]
                              · linarith only [h2204, h7, hlam]
                          · linarith only [h2201, h4, hlam]
                        · linarith only [h1, h2200, hlam]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h2142, h2151, h2155, h7, hc23, hc34, hlam, hphi, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h3, hlam, p2158_0]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h6, hlam, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        rcases p2158_3 (m.d 0 1) (by simp) with h2215 | h2215
                        · rcases p2158_3 (m.d 0 2) (by simp) with h2216 | h2216
                          · rcases p2158_3 (m.d 0 3) (by simp) with h2217 | h2217
                            · linarith only [h2063, h2217, hlam]
                            · rcases p2158_3 (m.d 0 4) (by simp) with h2219 | h2219
                              · rcases p2158_3 (m.d 0 5) (by simp) with h2220 | h2220
                                · rcases h2bigk with h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h0, h2144, h2150, h2151, h2155, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2221_1]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    rcases p2221_3 (m.d 0 2) (by simp) with h2224 | h2224
                                    · rcases p2221_3 (m.d 1 2) (by simp) with h2225 | h2225
                                      · linarith only [h0, h2225, hlam]
                                      · linarith only [h2143, h2225, hlam]
                                    · linarith only [h2224, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    rcases p2221_3 (m.d 0 2) (by simp) with h2229 | h2229
                                    · rcases p2221_3 (m.d 1 2) (by simp) with h2230 | h2230
                                      · linarith only [h0, h2230, hlam]
                                      · linarith only [h2144, h2230, hlam]
                                    · linarith only [h2229, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    rcases p2221_3 (m.d 0 2) (by simp) with h2234 | h2234
                                    · rcases p2221_3 (m.d 1 2) (by simp) with h2235 | h2235
                                      · linarith only [h0, h2235, hlam]
                                      · linarith only [h2145, h2235, hlam]
                                    · linarith only [h2234, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h0, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    rcases p2221_3 (m.d 0 2) (by simp) with h2241 | h2241
                                    · rcases p2221_3 (m.d 1 2) (by simp) with h2242 | h2242
                                      · rcases p2221_3 (m.d 2 3) (by simp) with h2243 | h2243
                                        · linarith only [h2243, hlam, p2221_0]
                                        · rcases p2221_3 (m.d 2 4) (by simp) with h2245 | h2245
                                          · linarith only [h2144, h2245, hlam]
                                          · linarith only [h2151, h2245, hlam]
                                      · linarith only [h2242, hlam, p2221_0]
                                    · linarith only [h2241, h4, hlam]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    rcases p2221_3 (m.d 0 2) (by simp) with h2250 | h2250
                                    · rcases p2221_3 (m.d 1 2) (by simp) with h2251 | h2251
                                      · rcases p2221_3 (m.d 2 3) (by simp) with h2252 | h2252
                                        · linarith only [h2143, h2252, hlam]
                                        · rcases p2221_3 (m.d 2 4) (by simp) with h2254 | h2254
                                          · linarith only [h2254, hlam, p2221_0]
                                          · rcases p2221_3 (m.d 2 5) (by simp) with h2256 | h2256
                                            · linarith only [h2145, h2256, hlam]
                                            · linarith only [h2155, h2256, hlam]
                                      · linarith only [h2251, hlam, p2221_0]
                                    · linarith only [h2250, h5, hlam]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2221_1, u5ehi2]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h4, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2143, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2151, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2153, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h5, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2144, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2150, h2155, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2221_1]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2155, hlam, p2221_1]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h6, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h2145, hlam, p2221_0]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h0, h2145, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2221_1]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [h0, h2144, h2150, h2155, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2221_1]
                                  · have p2221_0 := h2221c.1
                                    have p2221_1 := h2221c.2.1
                                    have p2221_2 := h2221c.2.2.1
                                    have p2221_3 := h2221c.2.2.2
                                    linarith only [hlam, p2221_0]
                                · linarith only [h2063, h2220, hlam]
                              · linarith only [h2219, h7, hlam]
                          · linarith only [h2216, h4, hlam]
                        · linarith only [h1, h2215, hlam]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [h2142, hlam, p2158_1]
                      · have p2158_0 := h2158c.1
                        have p2158_1 := h2158c.2.1
                        have p2158_2 := h2158c.2.2.1
                        have p2158_3 := h2158c.2.2.2
                        linarith only [hlam, p2158_0]
                    · linarith only [h0, h1, h2143, h2144, h2150, h2157, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2284 | h2284
              · linarith only [h1, h2142, h2143, h2150, h2284, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2286 | h2286
                · linarith only [h2063, h2286, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2288 | h2288
                  · linarith only [h2144, h2150, h2288, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2290 | h2290
                    · rcases h0bigk with h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2142, h2146, h2150, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        rcases p2291_3 (m.d 0 1) (by simp) with h2294 | h2294
                        · rcases p2291_3 (m.d 0 2) (by simp) with h2295 | h2295
                          · linarith only [h0, h2295, hlam]
                          · linarith only [h2295, h4, hlam]
                        · linarith only [h1, h2294, hlam]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2142, h2143, h2146, h2150, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        rcases p2291_3 (m.d 0 1) (by simp) with h2300 | h2300
                        · rcases p2291_3 (m.d 0 2) (by simp) with h2301 | h2301
                          · linarith only [h0, h2301, hlam]
                          · linarith only [h2301, h6, hlam]
                        · linarith only [h2300, h3, hlam]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h0, hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        rcases p2291_3 (m.d 0 1) (by simp) with h2307 | h2307
                        · rcases p2291_3 (m.d 0 2) (by simp) with h2308 | h2308
                          · rcases p2291_3 (m.d 0 3) (by simp) with h2309 | h2309
                            · linarith only [h2309, h4, hlam]
                            · rcases p2291_3 (m.d 0 4) (by simp) with h2311 | h2311
                              · linarith only [h2311, h5, hlam]
                              · linarith only [h2311, h7, hlam]
                          · linarith only [h2308, h4, hlam]
                        · linarith only [h1, h2307, hlam]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2142, h2143, h2146, h2150, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        rcases p2291_3 (m.d 0 1) (by simp) with h2317 | h2317
                        · rcases p2291_3 (m.d 0 2) (by simp) with h2318 | h2318
                          · rcases p2291_3 (m.d 0 3) (by simp) with h2319 | h2319
                            · linarith only [h2319, h4, hlam]
                            · rcases p2291_3 (m.d 0 4) (by simp) with h2321 | h2321
                              · linarith only [h2321, h5, hlam]
                              · linarith only [h2142, h2321, hlam]
                          · linarith only [h2318, h6, hlam]
                        · linarith only [h2317, h3, hlam]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h1, hlam, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h4, hlam, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h7, hlam, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2063, hlam, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2, hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h5, hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        rcases p2291_3 (m.d 0 1) (by simp) with h2333 | h2333
                        · rcases p2291_3 (m.d 0 2) (by simp) with h2334 | h2334
                          · rcases p2291_3 (m.d 0 3) (by simp) with h2335 | h2335
                            · linarith only [h2335, h7, hlam]
                            · rcases p2291_3 (m.d 0 4) (by simp) with h2337 | h2337
                              · rcases p2291_3 (m.d 0 5) (by simp) with h2338 | h2338
                                · linarith only [h2142, h2338, hlam]
                                · linarith only [h2063, h2338, hlam]
                              · linarith only [h2337, h7, hlam]
                          · linarith only [h2334, h4, hlam]
                        · linarith only [h1, h2333, hlam]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2142, h2143, h2146, h2150, h7, hc23, hc34, hlam, hphi, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h3, hlam, p2291_0]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h6, hlam, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        rcases p2291_3 (m.d 0 1) (by simp) with h2348 | h2348
                        · rcases p2291_3 (m.d 0 2) (by simp) with h2349 | h2349
                          · rcases p2291_3 (m.d 0 3) (by simp) with h2350 | h2350
                            · linarith only [h2063, h2350, hlam]
                            · rcases p2291_3 (m.d 0 4) (by simp) with h2352 | h2352
                              · rcases p2291_3 (m.d 0 5) (by simp) with h2353 | h2353
                                · rcases h2bigk with h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c | h2354c
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h0, h2145, hc01, hlam, hphi, ht0b, ht5b, p2354_1, u5ehi2]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    rcases p2354_3 (m.d 0 2) (by simp) with h2357 | h2357
                                    · rcases p2354_3 (m.d 1 2) (by simp) with h2358 | h2358
                                      · linarith only [h0, h2358, hlam]
                                      · linarith only [h2143, h2358, hlam]
                                    · linarith only [h2357, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    rcases p2354_3 (m.d 0 2) (by simp) with h2362 | h2362
                                    · rcases p2354_3 (m.d 1 2) (by simp) with h2363 | h2363
                                      · linarith only [h0, h2363, hlam]
                                      · linarith only [h2144, h2363, hlam]
                                    · linarith only [h2362, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    rcases p2354_3 (m.d 0 2) (by simp) with h2367 | h2367
                                    · rcases p2354_3 (m.d 1 2) (by simp) with h2368 | h2368
                                      · linarith only [h0, h2368, hlam]
                                      · linarith only [h2145, h2368, hlam]
                                    · linarith only [h2367, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h0, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    rcases p2354_3 (m.d 0 2) (by simp) with h2374 | h2374
                                    · rcases p2354_3 (m.d 1 2) (by simp) with h2375 | h2375
                                      · rcases p2354_3 (m.d 2 3) (by simp) with h2376 | h2376
                                        · linarith only [h2376, hlam, p2354_0]
                                        · rcases p2354_3 (m.d 2 4) (by simp) with h2378 | h2378
                                          · linarith only [h2144, h2378, hlam]
                                          · linarith only [h2284, h2378, hlam]
                                      · linarith only [h2375, hlam, p2354_0]
                                    · linarith only [h2374, h4, hlam]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    rcases p2354_3 (m.d 0 2) (by simp) with h2383 | h2383
                                    · rcases p2354_3 (m.d 1 2) (by simp) with h2384 | h2384
                                      · rcases p2354_3 (m.d 2 3) (by simp) with h2385 | h2385
                                        · linarith only [h2143, h2385, hlam]
                                        · rcases p2354_3 (m.d 2 4) (by simp) with h2387 | h2387
                                          · linarith only [h2387, hlam, p2354_0]
                                          · rcases p2354_3 (m.d 2 5) (by simp) with h2389 | h2389
                                            · linarith only [h2145, h2389, hlam]
                                            · linarith only [h2288, h2389, hlam]
                                      · linarith only [h2384, hlam, p2354_0]
                                    · linarith only [h2383, h5, hlam]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2354_1, u5ehi2]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h4, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h2143, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h2284, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h2286, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h5, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h2144, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h0, h2144, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2354_1]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h2288, hlam, p2354_1]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h6, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h2145, hlam, p2354_0]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h0, h2145, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2354_1]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [h0, h2145, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2354_1]
                                  · have p2354_0 := h2354c.1
                                    have p2354_1 := h2354c.2.1
                                    have p2354_2 := h2354c.2.2.1
                                    have p2354_3 := h2354c.2.2.2
                                    linarith only [hlam, p2354_0]
                                · linarith only [h2063, h2353, hlam]
                              · linarith only [h2352, h7, hlam]
                          · linarith only [h2349, h4, hlam]
                        · linarith only [h1, h2348, hlam]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [h2142, hlam, p2291_1]
                      · have p2291_0 := h2291c.1
                        have p2291_1 := h2291c.2.1
                        have p2291_2 := h2291c.2.2.1
                        have p2291_3 := h2291c.2.2.2
                        linarith only [hlam, p2291_0]
                    · linarith only [h2142, h2290, h7, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2417 | h2417
        · linarith only [h1, h2142, h2417, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2419 | h2419
          · linarith only [h1, h2063, h2419, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2421 | h2421
            · linarith only [h0, h2144, h2145, h2421, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2423 | h2423
              · linarith only [h0, h2143, h2145, h2423, h6, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2425 | h2425
                · linarith only [h1, h2063, h2143, h2425, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2427 | h2427
                  · linarith only [h0, h2144, h2145, h2417, h2421, h2427, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2142, h2143, h2145, h2427, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2430 | h2430
      · linarith only [h0, h2144, h2430, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2432 | h2432
        · linarith only [h1, h2142, h2432, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2434 | h2434
          · linarith only [h2143, h2144, h2434, h5, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2436 | h2436
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2437 | h2437
              · linarith only [h0, h2, h2436, h2437, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2439 | h2439
                · linarith only [h2063, h2142, h2143, h2430, h2439, h6, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2441 | h2441
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2442 | h2442
                    · rcases h0bigk with h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2430, h2441, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        rcases p2443_3 (m.d 0 1) (by simp) with h2446 | h2446
                        · rcases p2443_3 (m.d 0 2) (by simp) with h2447 | h2447
                          · linarith only [h0, h2447, hlam]
                          · linarith only [h2447, h4, hlam]
                        · linarith only [h1, h2446, hlam]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2, h2436, hc01, hlam, hphi, ht0b, ht5b, p2443_1, u5ehi4]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2143, h2430, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h0, hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        rcases p2443_3 (m.d 0 1) (by simp) with h2455 | h2455
                        · rcases p2443_3 (m.d 0 2) (by simp) with h2456 | h2456
                          · rcases p2443_3 (m.d 0 3) (by simp) with h2457 | h2457
                            · linarith only [h2457, h4, hlam]
                            · rcases p2443_3 (m.d 0 4) (by simp) with h2459 | h2459
                              · linarith only [h2459, h5, hlam]
                              · linarith only [h2459, h7, hlam]
                          · linarith only [h2456, h4, hlam]
                        · linarith only [h1, h2455, hlam]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2143, h2430, h2441, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h0, h2143, h2430, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h1, hlam, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h4, hlam, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h7, hlam, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2063, hlam, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2, hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h5, hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        rcases p2443_3 (m.d 0 1) (by simp) with h2473 | h2473
                        · rcases p2443_3 (m.d 0 2) (by simp) with h2474 | h2474
                          · rcases p2443_3 (m.d 0 3) (by simp) with h2475 | h2475
                            · linarith only [h2475, h7, hlam]
                            · rcases p2443_3 (m.d 0 4) (by simp) with h2477 | h2477
                              · rcases p2443_3 (m.d 0 5) (by simp) with h2478 | h2478
                                · linarith only [h2142, h2478, hlam]
                                · linarith only [h2063, h2478, hlam]
                              · linarith only [h2477, h7, hlam]
                          · linarith only [h2474, h4, hlam]
                        · linarith only [h1, h2473, hlam]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2143, h2430, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h3, hlam, p2443_0]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h6, hlam, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        rcases p2443_3 (m.d 0 1) (by simp) with h2488 | h2488
                        · rcases p2443_3 (m.d 0 2) (by simp) with h2489 | h2489
                          · rcases p2443_3 (m.d 0 3) (by simp) with h2490 | h2490
                            · linarith only [h2063, h2490, hlam]
                            · rcases p2443_3 (m.d 0 4) (by simp) with h2492 | h2492
                              · rcases p2443_3 (m.d 0 5) (by simp) with h2493 | h2493
                                · rcases h2bigk with h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    rcases p2494_3 (m.d 0 2) (by simp) with h2496 | h2496
                                    · rcases p2494_3 (m.d 1 2) (by simp) with h2497 | h2497
                                      · linarith only [h0, h2497, hlam]
                                      · rcases p2494_3 (m.d 2 3) (by simp) with h2499 | h2499
                                        · linarith only [h2499, h4, hlam]
                                        · rcases p2494_3 (m.d 2 4) (by simp) with h2501 | h2501
                                          · linarith only [h2501, h5, hlam]
                                          · linarith only [h2144, h2501, hlam]
                                    · linarith only [h0, h2496, hlam]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2143, h2430, h2441, h5, hlam, p2494_2]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2143, h2430, h2441, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2494_1]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h0, h2143, h2430, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2494_1]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h0, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h0, h2430, h2441, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2494_1]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2144, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2430, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h4, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2143, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2437, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2439, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h5, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h0, h2143, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2494_1]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    rcases p2494_3 (m.d 0 2) (by simp) with h2520 | h2520
                                    · rcases p2494_3 (m.d 1 2) (by simp) with h2521 | h2521
                                      · linarith only [h2144, h2521, hlam]
                                      · linarith only [h2143, h2521, hlam]
                                    · linarith only [h2520, h4, hlam]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, p2494_1, u5ehi2]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h6, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h0, h2143, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2494_1]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    rcases p2494_3 (m.d 0 2) (by simp) with h2529 | h2529
                                    · rcases p2494_3 (m.d 1 2) (by simp) with h2530 | h2530
                                      · linarith only [h2430, h2530, hlam]
                                      · linarith only [h2143, h2530, hlam]
                                    · linarith only [h2529, h4, hlam]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [h2441, hlam, p2494_0]
                                  · have p2494_0 := h2494c.1
                                    have p2494_1 := h2494c.2.1
                                    have p2494_2 := h2494c.2.2.1
                                    have p2494_3 := h2494c.2.2.2
                                    linarith only [hlam, p2494_0]
                                · linarith only [h2063, h2493, hlam]
                              · linarith only [h2492, h7, hlam]
                          · linarith only [h2489, h4, hlam]
                        · linarith only [h1, h2488, hlam]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [h2142, hlam, p2443_1]
                      · have p2443_0 := h2443c.1
                        have p2443_1 := h2443c.2.1
                        have p2443_2 := h2443c.2.2.1
                        have p2443_3 := h2443c.2.2.2
                        linarith only [hlam, p2443_0]
                    · linarith only [h2, h2436, h2442, h7, hlam]
                  · linarith only [h2143, h2144, h2436, h2441, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h2142, h2143, h2144, h2436, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2545 | h2545
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2546 | h2546
      · linarith only [h2063, h2143, h2546, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2548 | h2548
        · linarith only [h2143, h2545, h2548, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
        · linarith only [h2143, h2545, h2548, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2551 | h2551
      · linarith only [h0, h2545, h2551, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2553 | h2553
        · linarith only [h2143, h2553, h4, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2555 | h2555
          · linarith only [h1, h2063, h2143, h2555, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2557 | h2557
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2558 | h2558
              · linarith only [h2558, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2560 | h2560
                · linarith only [h2063, h2560, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2562 | h2562
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2563 | h2563
                    · rcases h0bigk with h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2143, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        rcases p2564_3 (m.d 0 1) (by simp) with h2567 | h2567
                        · rcases p2564_3 (m.d 0 2) (by simp) with h2568 | h2568
                          · linarith only [h0, h2568, hlam]
                          · linarith only [h2568, h4, hlam]
                        · linarith only [h1, h2567, hlam]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2, h2557, hc01, hlam, hphi, ht0b, ht5b, p2564_1, u5ehi4]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        rcases p2564_3 (m.d 0 1) (by simp) with h2573 | h2573
                        · rcases p2564_3 (m.d 0 2) (by simp) with h2574 | h2574
                          · linarith only [h0, h2574, hlam]
                          · linarith only [h2574, h6, hlam]
                        · linarith only [h2573, h3, hlam]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h0, hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        rcases p2564_3 (m.d 0 1) (by simp) with h2580 | h2580
                        · rcases p2564_3 (m.d 0 2) (by simp) with h2581 | h2581
                          · rcases p2564_3 (m.d 0 3) (by simp) with h2582 | h2582
                            · linarith only [h2582, h4, hlam]
                            · rcases p2564_3 (m.d 0 4) (by simp) with h2584 | h2584
                              · linarith only [h2584, h5, hlam]
                              · linarith only [h2584, h7, hlam]
                          · linarith only [h2581, h4, hlam]
                        · linarith only [h1, h2580, hlam]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2545, h2557, h5, hc02, hlam, hphi, ht0b, ht5b, p2564_1, u5ehi4]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        rcases p2564_3 (m.d 0 1) (by simp) with h2590 | h2590
                        · rcases p2564_3 (m.d 0 2) (by simp) with h2591 | h2591
                          · rcases p2564_3 (m.d 0 3) (by simp) with h2592 | h2592
                            · linarith only [h2592, h4, hlam]
                            · rcases p2564_3 (m.d 0 4) (by simp) with h2594 | h2594
                              · linarith only [h2594, h5, hlam]
                              · linarith only [h2142, h2594, hlam]
                          · linarith only [h2591, h6, hlam]
                        · linarith only [h2590, h3, hlam]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h1, hlam, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h4, hlam, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h7, hlam, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2063, hlam, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2, hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h5, hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2143, h4, h7, hc12, hc34, hlam, hphi, ht23, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2063, h2143, h4, h7, hc12, hc34, hlam, hphi, ht23, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h3, hlam, p2564_0]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h6, hlam, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2063, h2143, h4, hc12, hc35, hlam, hphi, ht23, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [h2142, hlam, p2564_1]
                      · have p2564_0 := h2564c.1
                        have p2564_1 := h2564c.2.1
                        have p2564_2 := h2564c.2.2.1
                        have p2564_3 := h2564c.2.2.2
                        linarith only [hlam, p2564_0]
                    · linarith only [h2, h2142, h2557, h2563, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · linarith only [h2545, h2557, h2562, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2616 | h2616
              · linarith only [h2142, h2553, h2557, h2616, h4, h7, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2618 | h2618
                · linarith only [h2063, h2618, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2620 | h2620
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2621 | h2621
                    · rcases h0bigk with h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2143, h2553, h2557, h2620, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        rcases p2622_3 (m.d 0 1) (by simp) with h2625 | h2625
                        · rcases p2622_3 (m.d 0 2) (by simp) with h2626 | h2626
                          · linarith only [h0, h2626, hlam]
                          · linarith only [h2626, h4, hlam]
                        · linarith only [h1, h2625, hlam]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2143, h2553, h2557, h2620, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        rcases p2622_3 (m.d 0 1) (by simp) with h2631 | h2631
                        · rcases p2622_3 (m.d 0 2) (by simp) with h2632 | h2632
                          · linarith only [h0, h2632, hlam]
                          · linarith only [h2632, h6, hlam]
                        · linarith only [h2631, h3, hlam]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h0, hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        rcases p2622_3 (m.d 0 1) (by simp) with h2638 | h2638
                        · rcases p2622_3 (m.d 0 2) (by simp) with h2639 | h2639
                          · rcases p2622_3 (m.d 0 3) (by simp) with h2640 | h2640
                            · linarith only [h2640, h4, hlam]
                            · rcases p2622_3 (m.d 0 4) (by simp) with h2642 | h2642
                              · linarith only [h2642, h5, hlam]
                              · linarith only [h2642, h7, hlam]
                          · linarith only [h2639, h4, hlam]
                        · linarith only [h1, h2638, hlam]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2143, h2553, h2557, h2620, h5, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        rcases p2622_3 (m.d 0 1) (by simp) with h2648 | h2648
                        · rcases p2622_3 (m.d 0 2) (by simp) with h2649 | h2649
                          · rcases p2622_3 (m.d 0 3) (by simp) with h2650 | h2650
                            · linarith only [h2650, h4, hlam]
                            · rcases p2622_3 (m.d 0 4) (by simp) with h2652 | h2652
                              · linarith only [h2652, h5, hlam]
                              · linarith only [h2142, h2652, hlam]
                          · linarith only [h2649, h6, hlam]
                        · linarith only [h2648, h3, hlam]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h1, hlam, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h4, hlam, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h7, hlam, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2063, hlam, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2, hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h5, hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2143, h4, h7, hc12, hc34, hlam, hphi, ht23, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2142, h2143, h2553, h2557, h7, hc12, hc34, hlam, hphi, ht23, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h3, hlam, p2622_0]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h6, hlam, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2063, h2143, h2621, h4, hc12, hc34, hlam, hphi, ht23, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [h2142, hlam, p2622_1]
                      · have p2622_0 := h2622c.1
                        have p2622_1 := h2622c.2.1
                        have p2622_2 := h2622c.2.2.1
                        have p2622_3 := h2622c.2.2.2
                        linarith only [hlam, p2622_0]
                    · linarith only [h2143, h2621, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2142, h2545, h2620, h7, hc12, hc34, hlam, hphi, ht23]

end R2N4
