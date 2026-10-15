import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1894 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2052 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2147 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2148 | h2148
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2149 | h2149
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2150 | h2150
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2151 | h2151
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2152 | h2152
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2153 | h2153
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2154 | h2154
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2155 | h2155
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2156 | h2156
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2157 | h2157
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2158 | h2158
                      · rcases h1bigk with h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h0, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h1769, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h1894, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2052, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          rcases p2159_3 (m.d 0 1) (by simp) with h2165 | h2165
                          · linarith only [h2165, hlam, p2159_0]
                          · rcases p2159_3 (m.d 1 2) (by simp) with h2167 | h2167
                            · rcases p2159_3 (m.d 1 3) (by simp) with h2168 | h2168
                              · linarith only [h2150, h2168, hlam]
                              · linarith only [h1769, h2168, hlam]
                            · linarith only [h2167, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h1769, hc01, hc12, hlam, hphi, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          rcases p2159_3 (m.d 0 1) (by simp) with h2176 | h2176
                          · linarith only [h2176, hlam, p2159_0]
                          · rcases p2159_3 (m.d 1 2) (by simp) with h2178 | h2178
                            · rcases p2159_3 (m.d 1 3) (by simp) with h2179 | h2179
                              · rcases p2159_3 (m.d 1 4) (by simp) with h2180 | h2180
                                · linarith only [h2153, h2180, hlam]
                                · linarith only [h1894, h2180, hlam]
                              · linarith only [h2179, hlam, p2159_0]
                            · linarith only [h0, h2178, hlam]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2150, hlam, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2052, h2155, hc01, hc13, hlam, hphi, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2052, h2150, hc01, hc12, hlam, hphi, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          rcases p2159_3 (m.d 0 1) (by simp) with h2189 | h2189
                          · linarith only [h2189, hlam, p2159_0]
                          · rcases p2159_3 (m.d 1 2) (by simp) with h2191 | h2191
                            · rcases p2159_3 (m.d 1 3) (by simp) with h2192 | h2192
                              · rcases p2159_3 (m.d 1 4) (by simp) with h2193 | h2193
                                · rcases p2159_3 (m.d 1 5) (by simp) with h2194 | h2194
                                  · linarith only [h2155, h2194, hlam]
                                  · linarith only [h2052, h2194, hlam]
                                · linarith only [h2193, hlam, p2159_0]
                              · linarith only [h1769, h2192, hlam]
                            · linarith only [h0, h2191, hlam]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2151, hlam, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2153, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2052, hc01, hc14, hlam, hphi, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          rcases p2159_3 (m.d 0 1) (by simp) with h2204 | h2204
                          · linarith only [h2204, hlam, p2159_0]
                          · rcases p2159_3 (m.d 1 2) (by simp) with h2206 | h2206
                            · rcases p2159_3 (m.d 1 3) (by simp) with h2207 | h2207
                              · rcases p2159_3 (m.d 1 4) (by simp) with h2208 | h2208
                                · rcases p2159_3 (m.d 1 5) (by simp) with h2209 | h2209
                                  · rcases h3bigk with h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h1769, hlam, p2210_1]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2156, h2158, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2210_1, u3ehi4]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      rcases p2210_3 (m.d 0 3) (by simp) with h2214 | h2214
                                      · rcases p2210_3 (m.d 1 3) (by simp) with h2215 | h2215
                                        · rcases p2210_3 (m.d 2 3) (by simp) with h2216 | h2216
                                          · linarith only [h2147, h2216, hlam]
                                          · linarith only [h2156, h2216, hlam]
                                        · linarith only [h2153, h2215, hlam]
                                      · linarith only [h2214, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      rcases p2210_3 (m.d 0 3) (by simp) with h2221 | h2221
                                      · rcases p2210_3 (m.d 1 3) (by simp) with h2222 | h2222
                                        · rcases p2210_3 (m.d 2 3) (by simp) with h2223 | h2223
                                          · linarith only [h2147, h2223, hlam]
                                          · linarith only [h2157, h2223, hlam]
                                        · linarith only [h2154, h2222, hlam]
                                      · linarith only [h2221, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2147, h2150, h2156, h2158, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2210_1, u3ehi4]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2150, h2156, h2158, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2210_1, u3ehi4]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      rcases p2210_3 (m.d 0 3) (by simp) with h2231 | h2231
                                      · linarith only [h1769, h2231, hlam]
                                      · linarith only [h2148, h2231, hlam]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      rcases p2210_3 (m.d 0 3) (by simp) with h2234 | h2234
                                      · linarith only [h1769, h2234, hlam]
                                      · linarith only [h2149, h2234, hlam]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2147, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2150, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2147, h2158, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2210_1, u3ehi4]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h0, h2147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2210_1, u3ehi4]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2148, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2153, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2156, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [hc34, hlam, hphi, p2210_1, u3ehi4]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2149, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2154, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2157, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [h2158, hlam, p2210_0]
                                    · have p2210_0 := h2210c.1
                                      have p2210_1 := h2210c.2.1
                                      have p2210_2 := h2210c.2.2.1
                                      have p2210_3 := h2210c.2.2.2
                                      linarith only [hlam, p2210_0]
                                  · linarith only [h2209, hlam, p2159_0]
                                · linarith only [h1894, h2208, hlam]
                              · linarith only [h1769, h2207, hlam]
                            · linarith only [h0, h2206, hlam]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2152, hlam, p2159_1]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2154, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [h2155, hlam, p2159_0]
                        · have p2159_0 := h2159c.1
                          have p2159_1 := h2159c.2.1
                          have p2159_2 := h2159c.2.2.1
                          have p2159_3 := h2159c.2.2.2
                          linarith only [hlam, p2159_0]
                      · rcases h1bigk with h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h0, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h1769, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h1894, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2052, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          rcases p2260_3 (m.d 0 1) (by simp) with h2266 | h2266
                          · linarith only [h2266, hlam, p2260_0]
                          · rcases p2260_3 (m.d 1 2) (by simp) with h2268 | h2268
                            · rcases p2260_3 (m.d 1 3) (by simp) with h2269 | h2269
                              · linarith only [h2150, h2269, hlam]
                              · linarith only [h1769, h2269, hlam]
                            · linarith only [h2268, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h1769, hc01, hc12, hlam, hphi, p2260_1]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2260_1]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2260_1]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          rcases p2260_3 (m.d 0 1) (by simp) with h2277 | h2277
                          · linarith only [h2277, hlam, p2260_0]
                          · rcases p2260_3 (m.d 1 2) (by simp) with h2279 | h2279
                            · rcases p2260_3 (m.d 1 3) (by simp) with h2280 | h2280
                              · rcases p2260_3 (m.d 1 4) (by simp) with h2281 | h2281
                                · linarith only [h2153, h2281, hlam]
                                · linarith only [h1894, h2281, hlam]
                              · linarith only [h2280, hlam, p2260_0]
                            · linarith only [h0, h2279, hlam]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2150, hlam, p2260_1]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2155, h2158, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2260_1, u3ehi3]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2150, h2155, h2158, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2260_1, u3ehi3]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          rcases p2260_3 (m.d 0 1) (by simp) with h2290 | h2290
                          · linarith only [h2290, hlam, p2260_0]
                          · rcases p2260_3 (m.d 1 2) (by simp) with h2292 | h2292
                            · rcases p2260_3 (m.d 1 3) (by simp) with h2293 | h2293
                              · rcases p2260_3 (m.d 1 4) (by simp) with h2294 | h2294
                                · rcases p2260_3 (m.d 1 5) (by simp) with h2295 | h2295
                                  · linarith only [h2155, h2295, hlam]
                                  · linarith only [h2052, h2295, hlam]
                                · linarith only [h2294, hlam, p2260_0]
                              · linarith only [h1769, h2293, hlam]
                            · linarith only [h0, h2292, hlam]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2151, hlam, p2260_1]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2153, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2155, h2158, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2260_1, u3ehi3]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          rcases p2260_3 (m.d 0 1) (by simp) with h2305 | h2305
                          · linarith only [h2305, hlam, p2260_0]
                          · rcases p2260_3 (m.d 1 2) (by simp) with h2307 | h2307
                            · rcases p2260_3 (m.d 1 3) (by simp) with h2308 | h2308
                              · rcases p2260_3 (m.d 1 4) (by simp) with h2309 | h2309
                                · rcases p2260_3 (m.d 1 5) (by simp) with h2310 | h2310
                                  · rcases h3bigk with h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h1769, hlam, p2311_1]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h1769, h2150, h2156, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2311_1, u3ehi3]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      rcases p2311_3 (m.d 0 3) (by simp) with h2315 | h2315
                                      · rcases p2311_3 (m.d 1 3) (by simp) with h2316 | h2316
                                        · rcases p2311_3 (m.d 2 3) (by simp) with h2317 | h2317
                                          · linarith only [h2147, h2317, hlam]
                                          · linarith only [h2156, h2317, hlam]
                                        · linarith only [h2153, h2316, hlam]
                                      · linarith only [h2315, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      rcases p2311_3 (m.d 0 3) (by simp) with h2322 | h2322
                                      · rcases p2311_3 (m.d 1 3) (by simp) with h2323 | h2323
                                        · rcases p2311_3 (m.d 2 3) (by simp) with h2324 | h2324
                                          · linarith only [h2147, h2324, hlam]
                                          · linarith only [h2157, h2324, hlam]
                                        · linarith only [h2154, h2323, hlam]
                                      · linarith only [h2322, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2147, h2150, h2157, h2158, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2311_1, u3ehi3]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2150, h2157, h2158, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2311_1, u3ehi3]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      rcases p2311_3 (m.d 0 3) (by simp) with h2332 | h2332
                                      · linarith only [h1769, h2332, hlam]
                                      · linarith only [h2148, h2332, hlam]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      rcases p2311_3 (m.d 0 3) (by simp) with h2335 | h2335
                                      · linarith only [h1769, h2335, hlam]
                                      · linarith only [h2149, h2335, hlam]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2147, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2150, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h0, h2147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2311_1, u3ehi3]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h0, h2147, h2158, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2311_1, u3ehi3]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2148, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2153, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2156, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2158, hlam, p2311_1]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2149, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2154, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [h2157, hlam, p2311_0]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2311_1, u3ehi3]
                                    · have p2311_0 := h2311c.1
                                      have p2311_1 := h2311c.2.1
                                      have p2311_2 := h2311c.2.2.1
                                      have p2311_3 := h2311c.2.2.2
                                      linarith only [hlam, p2311_0]
                                  · linarith only [h2310, hlam, p2260_0]
                                · linarith only [h1894, h2309, hlam]
                              · linarith only [h1769, h2308, hlam]
                            · linarith only [h0, h2307, hlam]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2152, hlam, p2260_1]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2154, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [h2155, hlam, p2260_0]
                        · have p2260_0 := h2260c.1
                          have p2260_1 := h2260c.2.1
                          have p2260_2 := h2260c.2.2.1
                          have p2260_3 := h2260c.2.2.2
                          linarith only [hlam, p2260_0]
                    · linarith only [h1769, h2149, h2150, h2156, h2157, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2362 | h2362
                    · linarith only [h2156, h2362, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2364 | h2364
                      · rcases h1bigk with h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h0, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h1769, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h1894, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2052, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          rcases p2365_3 (m.d 0 1) (by simp) with h2371 | h2371
                          · linarith only [h2371, hlam, p2365_0]
                          · rcases p2365_3 (m.d 1 2) (by simp) with h2373 | h2373
                            · rcases p2365_3 (m.d 1 3) (by simp) with h2374 | h2374
                              · linarith only [h2150, h2374, hlam]
                              · linarith only [h1769, h2374, hlam]
                            · linarith only [h2373, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h1769, h2148, h2362, h2364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2365_1, u3ehi2]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2365_1]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2365_1]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          rcases p2365_3 (m.d 0 1) (by simp) with h2382 | h2382
                          · linarith only [h2382, hlam, p2365_0]
                          · rcases p2365_3 (m.d 1 2) (by simp) with h2384 | h2384
                            · rcases p2365_3 (m.d 1 3) (by simp) with h2385 | h2385
                              · rcases p2365_3 (m.d 1 4) (by simp) with h2386 | h2386
                                · linarith only [h2153, h2386, hlam]
                                · linarith only [h1894, h2386, hlam]
                              · linarith only [h2385, hlam, p2365_0]
                            · linarith only [h0, h2384, hlam]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2150, hlam, p2365_1]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h1894, h2148, h2362, h2364, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2365_1, u3ehi2]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2052, h2149, h2150, h2362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2365_1, u3ehi2]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          rcases p2365_3 (m.d 0 1) (by simp) with h2395 | h2395
                          · linarith only [h2395, hlam, p2365_0]
                          · rcases p2365_3 (m.d 1 2) (by simp) with h2397 | h2397
                            · rcases p2365_3 (m.d 1 3) (by simp) with h2398 | h2398
                              · rcases p2365_3 (m.d 1 4) (by simp) with h2399 | h2399
                                · rcases p2365_3 (m.d 1 5) (by simp) with h2400 | h2400
                                  · linarith only [h2155, h2400, hlam]
                                  · linarith only [h2052, h2400, hlam]
                                · linarith only [h2399, hlam, p2365_0]
                              · linarith only [h1769, h2398, hlam]
                            · linarith only [h0, h2397, hlam]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2151, hlam, p2365_1]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2153, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2052, h2149, h2362, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2365_1, u3ehi2]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          rcases p2365_3 (m.d 0 1) (by simp) with h2410 | h2410
                          · linarith only [h2410, hlam, p2365_0]
                          · rcases p2365_3 (m.d 1 2) (by simp) with h2412 | h2412
                            · rcases p2365_3 (m.d 1 3) (by simp) with h2413 | h2413
                              · rcases p2365_3 (m.d 1 4) (by simp) with h2414 | h2414
                                · rcases p2365_3 (m.d 1 5) (by simp) with h2415 | h2415
                                  · rcases h3bigk with h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c | h2416c
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h1769, hlam, p2416_1]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      rcases p2416_3 (m.d 0 3) (by simp) with h2419 | h2419
                                      · rcases p2416_3 (m.d 1 3) (by simp) with h2420 | h2420
                                        · rcases p2416_3 (m.d 2 3) (by simp) with h2421 | h2421
                                          · linarith only [h2147, h2421, hlam]
                                          · rcases p2416_3 (m.d 3 4) (by simp) with h2423 | h2423
                                            · linarith only [h2148, h2423, hlam]
                                            · linarith only [h2156, h2423, hlam]
                                        · linarith only [h2150, h2420, hlam]
                                      · linarith only [h2147, h2419, hlam]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2147, h2362, h2364, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h0, h2147, h2362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2148, h2150, h2362, h2364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      rcases p2416_3 (m.d 0 3) (by simp) with h2432 | h2432
                                      · linarith only [h1769, h2432, hlam]
                                      · linarith only [h2147, h2432, hlam]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2150, h2362, h2364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2150, h2362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2147, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2150, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2156, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2362, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2148, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2153, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2148, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h1769, h2148, h2150, h2362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2149, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2154, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2416_1, u3ehi2]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [h2364, hlam, p2416_0]
                                    · have p2416_0 := h2416c.1
                                      have p2416_1 := h2416c.2.1
                                      have p2416_2 := h2416c.2.2.1
                                      have p2416_3 := h2416c.2.2.2
                                      linarith only [hlam, p2416_0]
                                  · linarith only [h2415, hlam, p2365_0]
                                · linarith only [h1894, h2414, hlam]
                              · linarith only [h1769, h2413, hlam]
                            · linarith only [h0, h2412, hlam]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2152, hlam, p2365_1]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2154, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [h2155, hlam, p2365_0]
                        · have p2365_0 := h2365c.1
                          have p2365_1 := h2365c.2.1
                          have p2365_2 := h2365c.2.2.1
                          have p2365_3 := h2365c.2.2.2
                          linarith only [hlam, p2365_0]
                      · linarith only [h2150, h2153, h2155, h2156, h2364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2461 | h2461
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2462 | h2462
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2463 | h2463
                      · linarith only [h1894, h2155, h2461, h2463, hc01, hc24, hlam, hphi, ht12]
                      · rcases h1bigk with h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h0, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1769, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1894, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2052, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          rcases p2465_3 (m.d 0 1) (by simp) with h2471 | h2471
                          · linarith only [h2471, hlam, p2465_0]
                          · rcases p2465_3 (m.d 1 2) (by simp) with h2473 | h2473
                            · rcases p2465_3 (m.d 1 3) (by simp) with h2474 | h2474
                              · linarith only [h2150, h2474, hlam]
                              · linarith only [h1769, h2474, hlam]
                            · linarith only [h2473, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1769, hc01, hc12, hlam, hphi, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1894, h2155, hc01, hc12, hlam, hphi, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          rcases p2465_3 (m.d 0 1) (by simp) with h2482 | h2482
                          · linarith only [h2482, hlam, p2465_0]
                          · rcases p2465_3 (m.d 1 2) (by simp) with h2484 | h2484
                            · rcases p2465_3 (m.d 1 3) (by simp) with h2485 | h2485
                              · rcases p2465_3 (m.d 1 4) (by simp) with h2486 | h2486
                                · linarith only [h2153, h2486, hlam]
                                · linarith only [h1894, h2486, hlam]
                              · linarith only [h2485, hlam, p2465_0]
                            · linarith only [h0, h2484, hlam]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2150, hlam, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1894, hc01, hc13, hlam, hphi, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1894, h2150, h2155, hc01, hc12, hlam, hphi, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2155, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2151, hlam, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2153, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2155, hlam, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          rcases p2465_3 (m.d 0 1) (by simp) with h2500 | h2500
                          · linarith only [h2500, hlam, p2465_0]
                          · rcases p2465_3 (m.d 1 2) (by simp) with h2502 | h2502
                            · rcases p2465_3 (m.d 1 3) (by simp) with h2503 | h2503
                              · rcases p2465_3 (m.d 1 4) (by simp) with h2504 | h2504
                                · linarith only [h2155, h2504, hlam]
                                · linarith only [h1894, h2504, hlam]
                              · linarith only [h1769, h2503, hlam]
                            · linarith only [h0, h2502, hlam]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2152, hlam, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h2154, hlam, p2465_0]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [h1894, hc01, hc15, hlam, hphi, p2465_1]
                        · have p2465_0 := h2465c.1
                          have p2465_1 := h2465c.2.1
                          have p2465_2 := h2465c.2.2.1
                          have p2465_3 := h2465c.2.2.2
                          linarith only [hlam, p2465_0]
                    · linarith only [h1769, h2149, h2150, h2461, h2462, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1894, h2148, h2155, h2461, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1769, h2149, h2154, hlam]
            · linarith only [h1769, h2149, h2153, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2517 | h2517
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2518 | h2518
              · linarith only [h2150, h2152, h2518, hlam]
              · linarith only [h1769, h2149, h2518, hlam]
            · linarith only [h1769, h2148, h2517, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2522 | h2522
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2523 | h2523
            · linarith only [h2150, h2151, h2523, hlam]
            · linarith only [h1769, h2148, h2523, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2526 | h2526
            · linarith only [h2150, h2151, h2526, hlam]
            · linarith only [h1769, h2148, h2526, hlam]
      · linarith only [h0, h2147, h2150, hlam]
    · linarith only [h2148, h2149, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2531 | h2531
    · linarith only [h2148, h2531, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2533 | h2533
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2534 | h2534
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2535 | h2535
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2536 | h2536
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2537 | h2537
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2538 | h2538
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2539 | h2539
                  · linarith only [h2147, h2531, h2539, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2541 | h2541
                    · linarith only [h2147, h2148, h2533, h2536, h2541, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2543 | h2543
                      · rcases h1bigk with h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c | h2544c
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h0, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h1769, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h1894, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2052, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          rcases p2544_3 (m.d 0 1) (by simp) with h2550 | h2550
                          · linarith only [h2550, hlam, p2544_0]
                          · rcases p2544_3 (m.d 1 2) (by simp) with h2552 | h2552
                            · rcases p2544_3 (m.d 1 3) (by simp) with h2553 | h2553
                              · linarith only [h2533, h2553, hlam]
                              · linarith only [h1769, h2553, hlam]
                            · linarith only [h2552, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2531, h2536, h2543, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2544_1, u3ehi0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2147, h2531, h2537, h2538, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2544_1, u3ehi2]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2147, h2531, h2537, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2544_1, u3ehi2]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          rcases p2544_3 (m.d 0 1) (by simp) with h2561 | h2561
                          · linarith only [h2561, hlam, p2544_0]
                          · rcases p2544_3 (m.d 1 2) (by simp) with h2563 | h2563
                            · rcases p2544_3 (m.d 1 3) (by simp) with h2564 | h2564
                              · rcases p2544_3 (m.d 1 4) (by simp) with h2565 | h2565
                                · linarith only [h2536, h2565, hlam]
                                · linarith only [h1894, h2565, hlam]
                              · linarith only [h2564, hlam, p2544_0]
                            · linarith only [h0, h2563, hlam]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2533, hlam, p2544_1]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2147, h2531, h2537, h2538, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2544_1, u3ehi2]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2147, h2531, h2533, h2537, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2544_1, u3ehi2]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          rcases p2544_3 (m.d 0 1) (by simp) with h2574 | h2574
                          · linarith only [h2574, hlam, p2544_0]
                          · rcases p2544_3 (m.d 1 2) (by simp) with h2576 | h2576
                            · rcases p2544_3 (m.d 1 3) (by simp) with h2577 | h2577
                              · rcases p2544_3 (m.d 1 4) (by simp) with h2578 | h2578
                                · rcases p2544_3 (m.d 1 5) (by simp) with h2579 | h2579
                                  · linarith only [h2538, h2579, hlam]
                                  · linarith only [h2052, h2579, hlam]
                                · linarith only [h2578, hlam, p2544_0]
                              · linarith only [h1769, h2577, hlam]
                            · linarith only [h0, h2576, hlam]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2534, hlam, p2544_1]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2536, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2147, h2531, h2537, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2544_1, u3ehi2]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          rcases p2544_3 (m.d 0 1) (by simp) with h2589 | h2589
                          · linarith only [h2589, hlam, p2544_0]
                          · rcases p2544_3 (m.d 1 2) (by simp) with h2591 | h2591
                            · rcases p2544_3 (m.d 1 3) (by simp) with h2592 | h2592
                              · rcases p2544_3 (m.d 1 4) (by simp) with h2593 | h2593
                                · rcases p2544_3 (m.d 1 5) (by simp) with h2594 | h2594
                                  · rcases h3bigk with h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h1769, hlam, p2595_1]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2531, h2543, hc34, hlam, hphi, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2148, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2531, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      rcases p2595_3 (m.d 0 3) (by simp) with h2601 | h2601
                                      · linarith only [h1769, h2601, hlam]
                                      · rcases p2595_3 (m.d 1 3) (by simp) with h2603 | h2603
                                        · rcases p2595_3 (m.d 2 3) (by simp) with h2604 | h2604
                                          · linarith only [h2533, h2604, hlam]
                                          · rcases p2595_3 (m.d 3 4) (by simp) with h2606 | h2606
                                            · linarith only [h2536, h2606, hlam]
                                            · linarith only [h2148, h2606, hlam]
                                        · linarith only [h1769, h2603, hlam]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      rcases p2595_3 (m.d 0 3) (by simp) with h2611 | h2611
                                      · linarith only [h1769, h2611, hlam]
                                      · linarith only [h2147, h2611, hlam]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2531, h2533, h2543, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2595_1, u3ehi0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2147, h2531, h2533, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2147, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2533, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2539, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2541, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2147, hc34, hlam, hphi, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2536, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2533, h2536, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2147, h2531, h2533, h2536, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2147, hc35, hlam, hphi, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2537, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2533, h2537, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2595_1, u3ehi2]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [h2543, hlam, p2595_0]
                                    · have p2595_0 := h2595c.1
                                      have p2595_1 := h2595c.2.1
                                      have p2595_2 := h2595c.2.2.1
                                      have p2595_3 := h2595c.2.2.2
                                      linarith only [hlam, p2595_0]
                                  · linarith only [h2594, hlam, p2544_0]
                                · linarith only [h1894, h2593, hlam]
                              · linarith only [h1769, h2592, hlam]
                            · linarith only [h0, h2591, hlam]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2535, hlam, p2544_1]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2537, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [h2538, hlam, p2544_0]
                        · have p2544_0 := h2544c.1
                          have p2544_1 := h2544c.2.1
                          have p2544_2 := h2544c.2.2.1
                          have p2544_3 := h2544c.2.2.2
                          linarith only [hlam, p2544_0]
                      · linarith only [h2147, h2148, h2543, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h2147, h2148, h2536, h2538, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h2147, h2148, h2536, h2537, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2642 | h2642
              · linarith only [h2536, h2642, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2644 | h2644
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2645 | h2645
                  · linarith only [h1769, h2536, h2645, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2647 | h2647
                    · linarith only [h2052, h2147, h2531, h2642, h2647, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2649 | h2649
                      · rcases h1bigk with h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h0, hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h1769, hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h1894, hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2052, hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          rcases p2650_3 (m.d 0 1) (by simp) with h2656 | h2656
                          · linarith only [h2656, hlam, p2650_0]
                          · rcases p2650_3 (m.d 1 2) (by simp) with h2658 | h2658
                            · rcases p2650_3 (m.d 1 3) (by simp) with h2659 | h2659
                              · linarith only [h2533, h2659, hlam]
                              · linarith only [h1769, h2659, hlam]
                            · linarith only [h2658, hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h1769, hc01, hc12, hlam, hphi, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h1894, hc01, hc12, hlam, hphi, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2052, hc01, hc12, hlam, hphi, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2642, hc01, hc35, hlam, hphi, ht12, ht23, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2533, hlam, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2536, hlam, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2642, hlam, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          rcases p2650_3 (m.d 0 1) (by simp) with h2672 | h2672
                          · linarith only [h2672, hlam, p2650_0]
                          · rcases p2650_3 (m.d 1 2) (by simp) with h2674 | h2674
                            · rcases p2650_3 (m.d 1 3) (by simp) with h2675 | h2675
                              · linarith only [h2536, h2675, hlam]
                              · linarith only [h1769, h2675, hlam]
                            · linarith only [h0, h2674, hlam]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2534, hlam, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h1769, hc01, hc14, hlam, hphi, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2052, h2147, h2531, h2536, hc34, hlam, hphi, p2650_1, u3ehi2]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          rcases p2650_3 (m.d 0 1) (by simp) with h2683 | h2683
                          · linarith only [h2683, hlam, p2650_0]
                          · rcases p2650_3 (m.d 1 2) (by simp) with h2685 | h2685
                            · rcases p2650_3 (m.d 1 3) (by simp) with h2686 | h2686
                              · linarith only [h2642, h2686, hlam]
                              · linarith only [h1769, h2686, hlam]
                            · linarith only [h0, h2685, hlam]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2535, hlam, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h1769, hc01, hc15, hlam, hphi, p2650_1]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [h2644, hlam, p2650_0]
                        · have p2650_0 := h2650c.1
                          have p2650_1 := h2650c.2.1
                          have p2650_2 := h2650c.2.2.1
                          have p2650_3 := h2650c.2.2.2
                          linarith only [hlam, p2650_0]
                      · linarith only [h2536, h2644, h2649, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2695 | h2695
                  · linarith only [h2147, h2148, h2695, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2697 | h2697
                    · linarith only [h1894, h2147, h2148, h2644, h2697, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2699 | h2699
                      · linarith only [h1894, h2148, h2644, h2699, hc34, hlam, hphi, u3ehi0]
                      · linarith only [h2147, h2148, h2699, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2702 | h2702
            · linarith only [h2147, h2148, h2533, h2535, h2702, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2704 | h2704
              · linarith only [h2147, h2531, h2533, h2535, h2704, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2706 | h2706
                · linarith only [h2534, h2535, h2706, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2708 | h2708
                  · linarith only [h0, h2147, h2535, h2708, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2710 | h2710
                    · linarith only [h0, h1769, h2147, h2535, h2704, h2710, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h2147, h2535, h2710, hc35, hlam, hphi, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2713 | h2713
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2714 | h2714
            · linarith only [h2148, h2533, h2534, h2714, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2716 | h2716
              · linarith only [h2714, h2716, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2718 | h2718
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2719 | h2719
                  · linarith only [h1769, h2714, h2719, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2147, h2534, h2719, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h2147, h2534, h2718, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2723 | h2723
            · linarith only [h2147, h2148, h2533, h2534, h2723, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2725 | h2725
              · linarith only [h2723, h2725, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2727 | h2727
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2728 | h2728
                  · linarith only [h2147, h2723, h2728, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h2147, h2534, h2728, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h2147, h2534, h2727, hc45, hlam, hphi, ht34, u3ehi2]
      · linarith only [h0, h2147, h2533, hlam]

end R2N4
