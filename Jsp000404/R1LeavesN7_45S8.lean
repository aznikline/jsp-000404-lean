import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_45S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_20_12_14_H_L_L_I_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h683 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1188 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1449 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2160 | h2160
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2161 | h2161
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2162 | h2162
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2163 | h2163
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2164 | h2164
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2165 | h2165
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2166 | h2166
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2167 | h2167
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2169 | h2169
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2170 | h2170
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2171 | h2171
                        · linarith only [h1449, h2160, h2171, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h1449, h2160, h2163, h2171, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1449, h2161, h2170, hlam]
                    · linarith only [h1449, h2160, h2162, h2163, h2169, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1188, h2160, h2163, h2168, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1449, h2162, h2164, h2167, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1449, h2160, h2164, h2166, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h1449, h2160, h2164, h2165, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2180 | h2180
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2181 | h2181
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2182 | h2182
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2183 | h2183
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2184 | h2184
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2185 | h2185
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2186 | h2186
                        · linarith only [h2160, h2186, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1449, h2160, h2163, h2186, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1188, h2164, h2180, h2185, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1188, h2164, h2180, h2184, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1188, h1449, h2160, h2163, h2183, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h2162, h2164, h2182, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1188, h2161, h2180, h2181, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h2160, h2180, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2195 | h2195
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2196 | h2196
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2197 | h2197
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2198 | h2198
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2199 | h2199
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2200 | h2200
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2201 | h2201
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2202 | h2202
                        · linarith only [h1449, h2160, h2163, h2195, h2202, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2204 | h2204
                          · linarith only [h1188, h1449, h2161, h2163, h2195, h2200, h2202, h2204, hc01, hc12, hlam, hphi]
                          · rcases h2bigk with h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1449, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1449, h2195, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1449, h2195, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              rcases p2206_3 (m.d 0 2) (by simp) with h2212 | h2212
                              · linarith only [h0, h2212, hlam]
                              · rcases p2206_3 (m.d 1 2) (by simp) with h2214 | h2214
                                · rcases p2206_3 (m.d 2 3) (by simp) with h2215 | h2215
                                  · linarith only [h2195, h2215, hlam]
                                  · linarith only [h1449, h2215, hlam]
                                · linarith only [h0, h2214, hlam]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1449, h2161, h2195, h2202, hlam, p2206_2]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1449, h2161, h2195, hlam, p2206_2]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2161, h2195, h2200, h2202, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2195, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              rcases p2206_3 (m.d 0 2) (by simp) with h2226 | h2226
                              · linarith only [h1449, h2226, hlam]
                              · linarith only [h2160, h2226, hlam]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              rcases p2206_3 (m.d 0 2) (by simp) with h2229 | h2229
                              · linarith only [h1449, h2229, hlam]
                              · linarith only [h2161, h2229, hlam]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2160, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2196, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2200, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2202, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2161, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2197, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2201, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2161, h2200, hc34, hlam, hphi, ht0b, ht45, ht5b, p2206_1, u0elo1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                      · linarith only [h1449, h2161, h2201, hlam]
                    · linarith only [h1449, h2162, h2200, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2244 | h2244
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2245 | h2245
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2246 | h2246
                        · linarith only [h2160, h2199, h2246, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2248 | h2248
                          · linarith only [h1188, h2199, h2248, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h2bigk with h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h0, hlam, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h1449, hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h1449, h2195, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h1449, h2195, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              rcases p2250_3 (m.d 0 2) (by simp) with h2256 | h2256
                              · linarith only [h0, h2256, hlam]
                              · rcases p2250_3 (m.d 1 2) (by simp) with h2258 | h2258
                                · rcases p2250_3 (m.d 2 3) (by simp) with h2259 | h2259
                                  · linarith only [h2195, h2259, hlam]
                                  · linarith only [h1449, h2259, hlam]
                                · linarith only [h0, h2258, hlam]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h1449, h2160, h2195, hlam, p2250_2]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h1449, h2161, h2195, hlam, p2250_2]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2161, h2195, h2245, h2248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2195, hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              rcases p2250_3 (m.d 0 2) (by simp) with h2270 | h2270
                              · linarith only [h1449, h2270, hlam]
                              · linarith only [h2160, h2270, hlam]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              rcases p2250_3 (m.d 0 2) (by simp) with h2273 | h2273
                              · linarith only [h1449, h2273, hlam]
                              · linarith only [h2161, h2273, hlam]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2160, hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2196, hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2244, hlam, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2246, hlam, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2161, hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2197, hlam, p2250_0]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2245, hlam, p2250_1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [h2161, hc24, hlam, hphi, ht0b, ht45, ht5b, p2250_1, u0elo1]
                            · have p2250_0 := h2250c.1
                              have p2250_1 := h2250c.2.1
                              have p2250_2 := h2250c.2.2.1
                              have p2250_3 := h2250c.2.2.2
                              linarith only [hlam, p2250_0]
                      · linarith only [h1449, h2161, h2245, hlam]
                    · linarith only [h1449, h2162, h2244, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1449, h2160, h2162, h2195, h2198, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h2161, h2197, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1449, h2195, h2196, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2291 | h2291
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2292 | h2292
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2293 | h2293
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2294 | h2294
                  · linarith only [h1188, h2163, h2195, h2291, h2294, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2296 | h2296
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2297 | h2297
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2298 | h2298
                        · linarith only [h2160, h2294, h2298, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2300 | h2300
                          · linarith only [h1188, h2294, h2296, h2300, hc01, hc24, hlam, hphi, ht12]
                          · rcases h2bigk with h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c | h2302c
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h0, hlam, p2302_1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h1449, hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h1449, hc24, hlam, hphi, ht0b, ht45, ht5b, p2302_1, u0elo2]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h1449, hc25, hlam, hphi, ht0b, ht5b, p2302_1, u0elo2]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2195, hc02, hc23, hlam, hphi, p2302_1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2195, hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              rcases p2302_3 (m.d 0 2) (by simp) with h2311 | h2311
                              · linarith only [h0, h2311, hlam]
                              · linarith only [h2160, h2311, hlam]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              rcases p2302_3 (m.d 0 2) (by simp) with h2314 | h2314
                              · linarith only [h0, h2314, hlam]
                              · linarith only [h2161, h2314, hlam]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              rcases p2302_3 (m.d 0 2) (by simp) with h2317 | h2317
                              · linarith only [h2317, hlam, p2302_0]
                              · rcases p2302_3 (m.d 1 2) (by simp) with h2319 | h2319
                                · linarith only [h2195, h2319, hlam]
                                · linarith only [h0, h2319, hlam]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2302_1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              rcases p2302_3 (m.d 0 2) (by simp) with h2324 | h2324
                              · linarith only [h1449, h2324, hlam]
                              · linarith only [h2160, h2324, hlam]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              rcases p2302_3 (m.d 0 2) (by simp) with h2327 | h2327
                              · linarith only [h1449, h2327, hlam]
                              · linarith only [h2161, h2327, hlam]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2160, hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2291, hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2296, hlam, p2302_1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2298, hlam, p2302_1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2161, hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2292, hlam, p2302_0]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2297, hlam, p2302_1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [h2161, h2296, hc34, hlam, hphi, ht0b, ht45, ht5b, p2302_1, u0elo1]
                            · have p2302_0 := h2302c.1
                              have p2302_1 := h2302c.2.1
                              have p2302_2 := h2302c.2.2.1
                              have p2302_3 := h2302c.2.2.2
                              linarith only [hlam, p2302_0]
                      · linarith only [h1188, h2195, h2292, h2294, h2297, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1188, h2195, h2292, h2294, h2296, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2162, h2195, h2293, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1188, h1449, h2161, h2291, h2292, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h2160, h2291, hlam]
      · linarith only [h1449, h2160, h2162, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2346 | h2346
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2347 | h2347
        · linarith only [h2160, h2161, h2347, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2349 | h2349
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2350 | h2350
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2351 | h2351
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2352 | h2352
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2353 | h2353
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2354 | h2354
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2355 | h2355
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2356 | h2356
                        · linarith only [h1449, h2160, h2347, h2356, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2358 | h2358
                          · linarith only [h2160, h2161, h2354, h2356, h2358, hlam]
                          · rcases h2bigk with h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h0, hlam, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h1449, hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2161, h2349, h2352, h2353, h2356, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2161, hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              rcases p2360_3 (m.d 0 2) (by simp) with h2366 | h2366
                              · linarith only [h0, h2366, hlam]
                              · rcases p2360_3 (m.d 1 2) (by simp) with h2368 | h2368
                                · rcases p2360_3 (m.d 2 3) (by simp) with h2369 | h2369
                                  · linarith only [h2349, h2369, hlam]
                                  · linarith only [h1449, h2369, hlam]
                                · linarith only [h0, h2368, hlam]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h0, h2161, h2355, hc01, hc12, hlam, hphi, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2160, h2161, h2349, h2355, hlam, p2360_2]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2160, h2161, h2354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2160, h2349, h2354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2349, hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              rcases p2360_3 (m.d 0 2) (by simp) with h2380 | h2380
                              · linarith only [h1449, h2380, hlam]
                              · linarith only [h2160, h2380, hlam]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2160, h2161, h2349, h2354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2160, hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2350, hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2354, hlam, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2356, hlam, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2160, h2351, h2354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2351, hlam, p2360_0]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [h2355, hlam, p2360_1]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              rcases p2360_3 (m.d 0 2) (by simp) with h2392 | h2392
                              · linarith only [h2161, h2392, hlam]
                              · linarith only [h2160, h2392, hlam]
                            · have p2360_0 := h2360c.1
                              have p2360_1 := h2360c.2.1
                              have p2360_2 := h2360c.2.2.1
                              have p2360_3 := h2360c.2.2.2
                              linarith only [hlam, p2360_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2396 | h2396
                        · linarith only [h1449, h2160, h2355, h2396, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2398 | h2398
                          · linarith only [h1449, h2160, h2354, h2355, h2396, h2398, hlam]
                          · linarith only [h1449, h2160, h2349, h2352, h2353, h2354, h2355, h2398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1449, h2160, h2346, h2354, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2402 | h2402
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2403 | h2403
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2404 | h2404
                        · linarith only [h2160, h2353, h2404, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2406 | h2406
                          · linarith only [h1188, h2160, h2353, h2402, h2406, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases h2bigk with h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h0, hlam, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h1449, hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2161, h2349, h2403, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2161, hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              rcases p2408_3 (m.d 0 2) (by simp) with h2414 | h2414
                              · linarith only [h0, h2414, hlam]
                              · rcases p2408_3 (m.d 1 2) (by simp) with h2416 | h2416
                                · rcases p2408_3 (m.d 2 3) (by simp) with h2417 | h2417
                                  · linarith only [h2349, h2417, hlam]
                                  · linarith only [h1449, h2417, hlam]
                                · linarith only [h0, h2416, hlam]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h0, h2161, h2403, hc01, hc12, hlam, hphi, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2160, h2161, h2349, h2403, hlam, p2408_2]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2160, h2161, h2402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2160, h2349, h2402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2349, hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              rcases p2408_3 (m.d 0 2) (by simp) with h2428 | h2428
                              · linarith only [h1449, h2428, hlam]
                              · linarith only [h2160, h2428, hlam]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2160, h2161, h2349, h2402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2160, hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2350, hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2402, hlam, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2404, hlam, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2160, h2351, h2402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2351, hlam, p2408_0]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [h2403, hlam, p2408_1]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              rcases p2408_3 (m.d 0 2) (by simp) with h2440 | h2440
                              · linarith only [h2161, h2440, hlam]
                              · linarith only [h2160, h2440, hlam]
                            · have p2408_0 := h2408c.1
                              have p2408_1 := h2408c.2.1
                              have p2408_2 := h2408c.2.2.1
                              have p2408_3 := h2408c.2.2.2
                              linarith only [hlam, p2408_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2444 | h2444
                        · linarith only [h1188, h2160, h2353, h2444, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2446 | h2446
                          · linarith only [h1188, h1449, h2160, h2353, h2402, h2403, h2446, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h1449, h2160, h2402, h2403, h2446, hc34, hc45, hlam, hphi]
                    · linarith only [h1449, h2346, h2402, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2346, h2352, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h1449, h2349, h2351, hc02, hc25, hlam, hphi]
            · linarith only [h1449, h2160, h2349, h2350, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2453 | h2453
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2454 | h2454
              · linarith only [h2160, h2161, h2349, h2454, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2456 | h2456
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2457 | h2457
                  · linarith only [h1188, h2347, h2349, h2453, h2457, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2459 | h2459
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2460 | h2460
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2461 | h2461
                        · linarith only [h2160, h2457, h2461, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2463 | h2463
                          · linarith only [h0, h2454, h2461, h2463, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h2bigk with h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h0, hlam, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h1449, hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h1449, hc24, hlam, hphi, ht0b, ht45, ht5b, p2465_1, u0elo2]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2161, hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2454, h2460, hc02, hc23, hlam, hphi, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2349, hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2454, h2459, h2461, hc34, hc45, hlam, hphi, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2454, hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              rcases p2465_3 (m.d 0 2) (by simp) with h2476 | h2476
                              · linarith only [h2476, hlam, p2465_0]
                              · rcases p2465_3 (m.d 1 2) (by simp) with h2478 | h2478
                                · linarith only [h2349, h2478, hlam]
                                · linarith only [h0, h2478, hlam]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              rcases p2465_3 (m.d 0 2) (by simp) with h2483 | h2483
                              · linarith only [h1449, h2483, hlam]
                              · linarith only [h2160, h2483, hlam]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2160, h2161, h2459, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2160, hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2453, hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2459, hlam, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [hlam, p2465_0]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2461, hlam, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2160, h2459, h2461, hc34, hc45, hlam, hphi, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h1188, h2453, hc01, hc25, hlam, hphi, ht12, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [h2460, hlam, p2465_1]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              rcases p2465_3 (m.d 0 2) (by simp) with h2495 | h2495
                              · linarith only [h2161, h2495, hlam]
                              · linarith only [h2160, h2495, hlam]
                            · have p2465_0 := h2465c.1
                              have p2465_1 := h2465c.2.1
                              have p2465_2 := h2465c.2.2.1
                              have p2465_3 := h2465c.2.2.2
                              linarith only [hlam, p2465_0]
                      · linarith only [h1188, h2349, h2453, h2460, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1188, h2349, h2453, h2459, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1188, h2346, h2349, h2453, h2456, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h2160, h2453, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h1449, h2160, h2346, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2504 | h2504
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2505 | h2505
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2506 | h2506
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2507 | h2507
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2508 | h2508
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2509 | h2509
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2510 | h2510
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2511 | h2511
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2512 | h2512
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2513 | h2513
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2514 | h2514
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2515 | h2515
                          · linarith only [h2505, h2515, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h2506, h2515, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h2160, h2506, h2514, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2160, h2504, h2512, h2513, hlam]
                    · linarith only [h2505, h2512, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2160, h2504, h2505, h2506, h2508, h2511, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h2505, h2510, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1449, h2504, h2507, h2509, hlam]
            · linarith only [h1449, h2504, h2507, h2508, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2525 | h2525
            · linarith only [h2160, h2504, h2507, h2525, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2527 | h2527
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2528 | h2528
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2529 | h2529
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2530 | h2530
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2531 | h2531
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2532 | h2532
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2533 | h2533
                          · linarith only [h2505, h2533, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h2505, h2506, h2533, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h2505, h2506, h2525, h2532, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h2525, h2530, h2531, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1449, h2505, h2530, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1188, h2506, h2529, hlam]
                · linarith only [h2505, h2528, h683, hlam]
              · linarith only [h0, h2504, h2527, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h2160, h2504, h2506, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2543 | h2543
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2544 | h2544
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2545 | h2545
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2546 | h2546
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2547 | h2547
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2548 | h2548
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2549 | h2549
                    · linarith only [h1449, h2504, h2505, h2544, h2549, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h1449, h2504, h2547, h2549, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h2543, h2548, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2553 | h2553
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2554 | h2554
                    · linarith only [h2547, h2554, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2556 | h2556
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2557 | h2557
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2558 | h2558
                          · rcases h2bigk with h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h0, hlam, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h1449, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2160, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h1449, h2544, h2547, h2556, h2558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              rcases p2559_3 (m.d 0 2) (by simp) with h2565 | h2565
                              · linarith only [h0, h2565, hlam]
                              · rcases p2559_3 (m.d 1 2) (by simp) with h2567 | h2567
                                · rcases p2559_3 (m.d 2 3) (by simp) with h2568 | h2568
                                  · linarith only [h2544, h2568, hlam]
                                  · linarith only [h1449, h2568, hlam]
                                · linarith only [h0, h2567, hlam]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h1449, h2504, h2554, h2556, h2558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h1449, h2504, h2544, hlam, p2559_2]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2504, h2544, h2556, h2558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2544, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2554, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              rcases p2559_3 (m.d 0 2) (by simp) with h2580 | h2580
                              · linarith only [h1449, h2580, hlam]
                              · linarith only [h2504, h2580, hlam]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2504, h2545, h2556, h2558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2545, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h1449, h2504, h2545, h2556, h2558, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              rcases p2559_3 (m.d 0 2) (by simp) with h2587 | h2587
                              · linarith only [h2160, h2587, hlam]
                              · linarith only [h2504, h2587, hlam]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2504, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2546, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2556, hlam, p2559_1]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [h2557, hlam, p2559_0]
                            · have p2559_0 := h2559c.1
                              have p2559_1 := h2559c.2.1
                              have p2559_2 := h2559c.2.2.1
                              have p2559_3 := h2559c.2.2.2
                              linarith only [hlam, p2559_0]
                          · linarith only [h2547, h2558, h683, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h2543, h2557, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h1449, h2504, h2556, hlam]
                  · linarith only [h2543, h2553, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h2504, h2546, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1449, h2544, h2545, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2601 | h2601
            · linarith only [h2160, h2504, h2544, h2601, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2603 | h2603
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2604 | h2604
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2605 | h2605
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2606 | h2606
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2607 | h2607
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2608 | h2608
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2609 | h2609
                          · rcases h2bigk with h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h0, hlam, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h1449, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2160, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2607, h2609, hc45, hlam, hphi, ht0b, ht5b, p2610_1, u0elo1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2601, h2606, hc02, hc23, hlam, hphi, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2544, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2601, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              rcases p2610_3 (m.d 0 2) (by simp) with h2620 | h2620
                              · linarith only [h0, h2620, hlam]
                              · linarith only [h2504, h2620, hlam]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              rcases p2610_3 (m.d 0 2) (by simp) with h2623 | h2623
                              · linarith only [h2623, hlam, p2610_0]
                              · rcases p2610_3 (m.d 1 2) (by simp) with h2625 | h2625
                                · linarith only [h2544, h2625, hlam]
                                · linarith only [h0, h2625, hlam]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2160, h2504, h2607, h2609, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h1449, h2504, h2505, h2544, h2604, hlam, p2610_2]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              rcases p2610_3 (m.d 0 2) (by simp) with h2632 | h2632
                              · linarith only [h2632, hlam, p2610_0]
                              · rcases p2610_3 (m.d 1 2) (by simp) with h2634 | h2634
                                · linarith only [h2601, h2634, hlam]
                                · linarith only [h0, h2634, hlam]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2606, hlam, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              rcases p2610_3 (m.d 0 2) (by simp) with h2640 | h2640
                              · linarith only [h2160, h2640, hlam]
                              · linarith only [h2504, h2640, hlam]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2504, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2603, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2607, hlam, p2610_1]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [h2608, hlam, p2610_0]
                            · have p2610_0 := h2610c.1
                              have p2610_1 := h2610c.2.1
                              have p2610_2 := h2610c.2.2.1
                              have p2610_3 := h2610c.2.2.2
                              linarith only [hlam, p2610_0]
                          · linarith only [h1449, h2505, h2543, h2609, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h2543, h2601, h2608, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h1449, h2505, h2544, h2604, h2607, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h2544, h2604, h2606, hlam]
                  · linarith only [h1449, h2504, h2505, h2543, h2604, h2605, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2653 | h2653
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2654 | h2654
                    · linarith only [h2604, h2654, h683, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h2544, h2654, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2543, h2544, h2604, h2653, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h2504, h2603, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h1449, h2504, h2505, h2543, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2660 | h2660
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2661 | h2661
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2662 | h2662
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2663 | h2663
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2664 | h2664
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2665 | h2665
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2666 | h2666
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2667 | h2667
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2668 | h2668
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2669 | h2669
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2670 | h2670
                          · linarith only [h2660, h2670, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h2660, h2661, h2670, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h2660, h2661, h2669, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2674 | h2674
                        · linarith only [h2667, h2668, h2674, hlam]
                        · linarith only [h2160, h2660, h2661, h2674, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1449, h2660, h2667, hlam]
                  · linarith only [h1188, h2661, h2666, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h1449, h2660, h2662, h2665, hlam]
              · linarith only [h0, h1449, h2662, h2664, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h1449, h2662, h2663, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2682 | h2682
            · linarith only [h0, h2160, h2662, h2682, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2684 | h2684
              · linarith only [h0, h2504, h2662, h2684, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2686 | h2686
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2687 | h2687
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2688 | h2688
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2689 | h2689
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2690 | h2690
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2691 | h2691
                          · linarith only [h2660, h2691, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h2660, h2661, h2691, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h2660, h2661, h2690, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h2662, h2689, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h2662, h2688, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1188, h2661, h2687, hlam]
                · linarith only [h2660, h2686, h683, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2699 | h2699
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2700 | h2700
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2701 | h2701
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2702 | h2702
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2703 | h2703
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2704 | h2704
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2705 | h2705
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2706 | h2706
                        · linarith only [h1188, h2661, h2699, h2704, h2706, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2160, h2699, h2702, h2703, h2706, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2709 | h2709
                        · linarith only [h0, h2160, h2661, h2700, h2709, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2160, h2699, h2702, h2703, h2709, hc01, hc12, hlam, hphi]
                    · linarith only [h2660, h2704, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2713 | h2713
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2714 | h2714
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2715 | h2715
                        · linarith only [h1188, h2703, h2715, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2717 | h2717
                          · linarith only [h0, h2160, h2660, h2700, h2703, h2717, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases h2bigk with h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c | h2719c
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, hlam, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h1449, hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2160, hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2504, hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              rcases p2719_3 (m.d 0 2) (by simp) with h2725 | h2725
                              · linarith only [h0, h2725, hlam]
                              · rcases p2719_3 (m.d 1 2) (by simp) with h2727 | h2727
                                · rcases p2719_3 (m.d 2 3) (by simp) with h2728 | h2728
                                  · linarith only [h2699, h2728, hlam]
                                  · linarith only [h1449, h2728, hlam]
                                · linarith only [h0, h2727, hlam]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2160, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2504, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2699, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2699, hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2160, h2699, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2504, h2699, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2700, h2703, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2700, hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2713, hlam, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2715, hlam, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2701, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2701, hlam, p2719_0]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h2714, hlam, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [h0, h2160, h2699, h2714, hc01, hc12, hlam, hphi, p2719_1]
                            · have p2719_0 := h2719c.1
                              have p2719_1 := h2719c.2.1
                              have p2719_2 := h2719c.2.2.1
                              have p2719_3 := h2719c.2.2.2
                              linarith only [hlam, p2719_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2751 | h2751
                        · linarith only [h1188, h2703, h2751, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2753 | h2753
                          · linarith only [h0, h2160, h2660, h2700, h2703, h2753, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases h2bigk with h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, hlam, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h1449, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2160, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2504, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              rcases p2755_3 (m.d 0 2) (by simp) with h2761 | h2761
                              · linarith only [h0, h2761, hlam]
                              · rcases p2755_3 (m.d 1 2) (by simp) with h2763 | h2763
                                · rcases p2755_3 (m.d 2 3) (by simp) with h2764 | h2764
                                  · linarith only [h2699, h2764, hlam]
                                  · linarith only [h1449, h2764, hlam]
                                · linarith only [h0, h2763, hlam]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2160, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2504, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2699, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2699, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2160, h2699, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2714, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2700, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2700, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2713, hlam, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2751, hlam, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2701, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h2701, hlam, p2755_0]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h1449, h2701, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [h0, h2160, h2701, hc01, hc12, hlam, hphi, p2755_1]
                            · have p2755_0 := h2755c.1
                              have p2755_1 := h2755c.2.1
                              have p2755_2 := h2755c.2.2.1
                              have p2755_3 := h2755c.2.2.2
                              linarith only [hlam, p2755_0]
                    · linarith only [h1449, h2660, h2713, hlam]
                · linarith only [h2660, h2702, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h1449, h2699, h2701, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h1449, h2699, h2700, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2791 | h2791
            · linarith only [h0, h2160, h2699, h2791, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2793 | h2793
              · linarith only [h0, h2504, h2699, h2793, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2795 | h2795
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2796 | h2796
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2797 | h2797
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2798 | h2798
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2799 | h2799
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2800 | h2800
                          · linarith only [h0, h2160, h2660, h2661, h2800, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases h2bigk with h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, hlam, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h1449, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2160, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2504, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, h2793, h2797, h2799, hc01, hc23, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2699, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2791, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2793, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              rcases p2802_3 (m.d 0 2) (by simp) with h2813 | h2813
                              · linarith only [h2813, hlam, p2802_0]
                              · rcases p2802_3 (m.d 1 2) (by simp) with h2815 | h2815
                                · linarith only [h2699, h2815, hlam]
                                · linarith only [h0, h2815, hlam]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, h2160, hc01, hc23, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, h2793, hc01, hc23, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              rcases p2802_3 (m.d 0 2) (by simp) with h2822 | h2822
                              · linarith only [h2822, hlam, p2802_0]
                              · rcases p2802_3 (m.d 1 2) (by simp) with h2824 | h2824
                                · linarith only [h2791, h2824, hlam]
                                · linarith only [h0, h2824, hlam]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2797, hlam, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, h2793, h2797, hc01, hc23, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              rcases p2802_3 (m.d 0 2) (by simp) with h2831 | h2831
                              · linarith only [h2831, hlam, p2802_0]
                              · rcases p2802_3 (m.d 1 2) (by simp) with h2833 | h2833
                                · linarith only [h2793, h2833, hlam]
                                · linarith only [h0, h2833, hlam]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2798, hlam, p2802_1]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [h2799, hlam, p2802_0]
                            · have p2802_0 := h2802c.1
                              have p2802_1 := h2802c.2.1
                              have p2802_2 := h2802c.2.2.1
                              have p2802_3 := h2802c.2.2.2
                              linarith only [hlam, p2802_0]
                        · linarith only [h0, h2160, h2795, h2796, h2799, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h2160, h2661, h2699, h2795, h2796, h2798, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h2660, h2661, h2699, h2795, h2796, h2797, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2843 | h2843
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2844 | h2844
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2845 | h2845
                        · linarith only [h1188, h2796, h2845, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h2791, h2845, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h2699, h2844, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h2660, h2699, h2843, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h2660, h2795, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2851 | h2851
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2852 | h2852
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2853 | h2853
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2854 | h2854
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2855 | h2855
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2856 | h2856
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2857 | h2857
                    · linarith only [h2660, h2852, h2857, h683, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h1449, h2852, h2855, h2857, hc01, hc12, hlam, hphi]
                  · linarith only [h2851, h2856, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2861 | h2861
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2862 | h2862
                    · linarith only [h2855, h2862, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2864 | h2864
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2865 | h2865
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2866 | h2866
                          · rcases h2bigk with h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c | h2867c
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, hlam, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h1449, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2160, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2504, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              rcases p2867_3 (m.d 0 2) (by simp) with h2873 | h2873
                              · linarith only [h0, h2873, hlam]
                              · rcases p2867_3 (m.d 1 2) (by simp) with h2875 | h2875
                                · rcases p2867_3 (m.d 2 3) (by simp) with h2876 | h2876
                                  · linarith only [h2852, h2876, hlam]
                                  · linarith only [h1449, h2876, hlam]
                                · linarith only [h0, h2875, hlam]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2504, h2862, h2864, hc01, hc12, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2504, hc01, hc12, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2852, h2855, hc01, hc34, hlam, hphi, ht12, ht23, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2852, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2862, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2504, h2852, h2855, hc01, hc34, hlam, hphi, ht12, ht23, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2853, hc01, hc12, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2853, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h1449, h2853, hc01, hc14, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2504, h2853, hc01, hc12, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h0, h2852, h2864, hc01, hc12, hlam, hphi, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2854, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2864, hlam, p2867_1]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [h2865, hlam, p2867_0]
                            · have p2867_0 := h2867c.1
                              have p2867_1 := h2867c.2.1
                              have p2867_2 := h2867c.2.2.1
                              have p2867_3 := h2867c.2.2.2
                              linarith only [hlam, p2867_0]
                          · linarith only [h2851, h2855, h2866, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h2851, h2865, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2901 | h2901
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2902 | h2902
                          · rcases h2bigk with h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c | h2903c
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, hlam, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h1449, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2160, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2504, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              rcases p2903_3 (m.d 0 2) (by simp) with h2909 | h2909
                              · linarith only [h0, h2909, hlam]
                              · rcases p2903_3 (m.d 1 2) (by simp) with h2911 | h2911
                                · rcases p2903_3 (m.d 2 3) (by simp) with h2912 | h2912
                                  · linarith only [h2852, h2912, hlam]
                                  · linarith only [h1449, h2912, hlam]
                                · linarith only [h0, h2911, hlam]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h1449, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h2160, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h1449, h2864, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h2864, hc01, hc35, hlam, hphi, ht12, ht23, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2852, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2862, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2864, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h2853, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2853, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h1449, h2853, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h1449, h2853, h2864, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h2854, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2854, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h0, h1449, h2854, hc01, hc12, hlam, hphi, p2903_1]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [h2901, hlam, p2903_0]
                            · have p2903_0 := h2903c.1
                              have p2903_1 := h2903c.2.1
                              have p2903_2 := h2903c.2.2.1
                              have p2903_3 := h2903c.2.2.2
                              linarith only [hlam, p2903_0]
                          · linarith only [h2851, h2855, h2902, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h2851, h2901, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h2851, h2861, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h0, h1449, h2852, h2854, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h1449, h2852, h2853, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2940 | h2940
            · linarith only [h0, h2160, h2852, h2940, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2942 | h2942
              · linarith only [h0, h2504, h2940, h2942, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2944 | h2944
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2945 | h2945
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2946 | h2946
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2947 | h2947
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2948 | h2948
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2949 | h2949
                          · rcases h2bigk with h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, hlam, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h1449, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2160, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2504, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, h2942, h2946, h2948, hc01, hc23, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2852, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2940, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2942, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              rcases p2950_3 (m.d 0 2) (by simp) with h2961 | h2961
                              · linarith only [h2961, hlam, p2950_0]
                              · rcases p2950_3 (m.d 1 2) (by simp) with h2963 | h2963
                                · linarith only [h2852, h2963, hlam]
                                · linarith only [h0, h2963, hlam]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, h2160, hc01, hc23, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, h2942, hc01, hc23, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              rcases p2950_3 (m.d 0 2) (by simp) with h2970 | h2970
                              · linarith only [h2970, hlam, p2950_0]
                              · rcases p2950_3 (m.d 1 2) (by simp) with h2972 | h2972
                                · linarith only [h2940, h2972, hlam]
                                · linarith only [h0, h2972, hlam]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2946, hlam, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, h2942, h2946, hc01, hc23, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              rcases p2950_3 (m.d 0 2) (by simp) with h2979 | h2979
                              · linarith only [h2979, hlam, p2950_0]
                              · rcases p2950_3 (m.d 1 2) (by simp) with h2981 | h2981
                                · linarith only [h2942, h2981, hlam]
                                · linarith only [h0, h2981, hlam]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2947, hlam, p2950_1]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [h2948, hlam, p2950_0]
                            · have p2950_0 := h2950c.1
                              have p2950_1 := h2950c.2.1
                              have p2950_2 := h2950c.2.2.1
                              have p2950_3 := h2950c.2.2.2
                              linarith only [hlam, p2950_0]
                          · linarith only [h2660, h2851, h2949, hlam]
                        · linarith only [h2851, h2948, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h2852, h2947, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h2852, h2944, h2946, hlam]
                  · linarith only [h2660, h2851, h2944, h2945, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2993 | h2993
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2994 | h2994
                    · linarith only [h2944, h2994, h683, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h2852, h2994, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1188, h2851, h2993, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2998 | h2998
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2999 | h2999
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3000 | h3000
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3001 | h3001
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3002 | h3002
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3003 | h3003
                    · linarith only [h0, h1449, h2660, h2998, h3003, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h1449, h2998, h3001, h3003, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3006 | h3006
                    · linarith only [h0, h1449, h2660, h2998, h3006, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h1449, h3001, h3002, h3006, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3009 | h3009
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3010 | h3010
                    · linarith only [h3001, h3010, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3012 | h3012
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3013 | h3013
                        · linarith only [h0, h1449, h2660, h2851, h2999, h3013, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2160, h3009, h3013, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3016 | h3016
                        · linarith only [h0, h1449, h2660, h2851, h2999, h3016, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2160, h3001, h3009, h3016, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3019 | h3019
                    · linarith only [h0, h1449, h2660, h2998, h3019, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3021 | h3021
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3022 | h3022
                        · linarith only [h1188, h3009, h3022, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h3019, h3021, h3022, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3025 | h3025
                        · linarith only [h3001, h3009, h3025, h683, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3027 | h3027
                          · linarith only [h0, h1449, h2998, h3001, h3009, h3027, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h1449, h2998, h3001, h3027, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h1449, h2998, h3000, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h1449, h2998, h2999, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3032 | h3032
            · linarith only [h0, h2160, h2998, h3032, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3034 | h3034
              · linarith only [h0, h2504, h2998, h3034, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3036 | h3036
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3037 | h3037
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3038 | h3038
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3039 | h3039
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3040 | h3040
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3041 | h3041
                          · linarith only [h0, h1449, h2660, h2851, h3036, h3041, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h1449, h2660, h3037, h3041, hc01, hc14, hlam, hphi]
                        · linarith only [h3032, h3037, h3040, hlam]
                      · linarith only [h0, h1449, h2660, h2851, h3032, h3037, h3038, h3039, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h1449, h2660, h2851, h2998, h3036, h3037, h3038, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3047 | h3047
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3048 | h3048
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3049 | h3049
                        · linarith only [h1188, h3037, h3047, h3049, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3032, h3049, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h2998, h3048, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h2998, h3036, h3047, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3054 | h3054
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3055 | h3055
                    · linarith only [h3036, h3055, h683, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h2998, h3055, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3058 | h3058
                    · linarith only [h0, h2998, h3036, h3058, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h2998, h3058, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_20_12_14_H_L_L_I_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h683 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1188 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1449 | h1449
  · exact r1l7_20_12_14_H_L_L_I_L_I_x1_x1_x1_x0 m hb0 hb2 hb4 h0 h683 h1188 h1449
  · exact r1l7_20_12_14_H_L_L_I_L_I_x1_x1_x1_x1 m hb0 hb2 hb4 h0 h683 h1188 h1449

end R2N4
