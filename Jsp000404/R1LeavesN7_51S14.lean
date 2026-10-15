import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S12
import Jsp000404.R1LeavesN7_51S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1475 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1633 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1778 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2121 | h2121
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2122 | h2122
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2123 | h2123
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2124 | h2124
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2125 | h2125
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2126 | h2126
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2127 | h2127
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2128 | h2128
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2129 | h2129
                  · linarith only [h1778, h2121, h2124, h2129, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1778, h2121, h2122, h2129, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1778, h2121, h2123, h2124, h2128, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h1314, h2122, h2127, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1778, h2121, h2122, h2124, h2126, hlam]
          · linarith only [h1778, h2121, h2124, h2125, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2136 | h2136
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2137 | h2137
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2138 | h2138
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2139 | h2139
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2140 | h2140
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2141 | h2141
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2142 | h2142
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2143 | h2143
                        · rcases h4bigk with h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h1475, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2141, h2142, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2144_1, u3ehi4]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2121, h2143, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2144_1, u3ehi4]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h0, h2121, h2124, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h1475, hc01, hc14, hlam, hphi, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2124, h2136, h2141, h2142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2144_1, u3ehi4]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2124, h2136, h2143, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2144_1, u3ehi4]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2124, h2136, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2121, hlam, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2136, hlam, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2121, h2143, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2144_1, u3ehi4]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h0, h2121, h2124, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2122, hlam, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2137, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2140, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2122, hc03, hc45, hlam, hphi, ht0b, ht5b, p2144_1]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2123, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2139, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2142, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [h2143, hlam, p2144_0]
                          · have p2144_0 := h2144c.1
                            have p2144_1 := h2144c.2.1
                            have p2144_2 := h2144c.2.2.1
                            have p2144_3 := h2144c.2.2.2
                            linarith only [hlam, p2144_0]
                        · linarith only [h1475, h2123, h2124, h2136, h2143, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1475, h2123, h2124, h2136, h2140, h2142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h2124, h2141, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1633, h2122, h2124, h2136, h2139, h2140, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h1475, h2123, h2139, hlam]
              · linarith only [h1314, h2122, h2138, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1314, h2122, h2137, hlam]
          · linarith only [h0, h2121, h2136, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2178 | h2178
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2179 | h2179
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2180 | h2180
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2181 | h2181
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2182 | h2182
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2183 | h2183
                  · linarith only [h1778, h2121, h2178, h2183, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1778, h2122, h2123, h2180, h2182, h2183, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2186 | h2186
                  · linarith only [h1778, h2121, h2178, h2186, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1778, h2122, h2186, hlam]
              · linarith only [h1314, h2122, h2181, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1778, h2121, h2122, h2178, h2180, hlam]
          · linarith only [h1778, h2121, h2178, h2179, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2192 | h2192
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2193 | h2193
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2194 | h2194
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2195 | h2195
                · linarith only [h2122, h2123, h2178, h2192, h2195, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2197 | h2197
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2198 | h2198
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2199 | h2199
                      · linarith only [h1475, h2121, h2195, h2199, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2201 | h2201
                        · linarith only [h0, h1475, h2121, h2178, h2195, h2197, h2201, hc01, hc23, hlam, hphi, ht12]
                        · rcases h4bigk with h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h1475, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2197, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2123, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2195, hc04, hc45, hlam, hphi, p2203_1]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2195, h2197, hc45, hlam, hphi, ht34, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2195, hc45, hlam, hphi, ht34, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2195, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2121, hlam, p2203_1]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2192, hlam, p2203_1]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h0, h2121, h2178, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2199, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2122, hlam, p2203_1]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2193, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2197, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2201, hlam, p2203_0]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p2203_1]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hc14, hc45, hlam, hphi, p2203_1]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [h2197, hc45, hlam, hphi, ht34, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p2203_1, u3ehi3]
                          · have p2203_0 := h2203c.1
                            have p2203_1 := h2203c.2.1
                            have p2203_2 := h2203c.2.2.1
                            have p2203_3 := h2203c.2.2.2
                            linarith only [hlam, p2203_0]
                    · linarith only [h2178, h2194, h2198, hlam]
                  · linarith only [h2178, h2194, h2197, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1314, h2122, h2194, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1314, h2122, h2193, hlam]
          · linarith only [h0, h2121, h2192, hlam]
    · linarith only [h1778, h2121, h2122, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2235 | h2235
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2236 | h2236
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2237 | h2237
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2238 | h2238
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2239 | h2239
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2240 | h2240
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2241 | h2241
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2242 | h2242
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2243 | h2243
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2244 | h2244
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2245 | h2245
                        · rcases h4bigk with h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h1475, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2121, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2245, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2246_1, u3ehi4]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h1778, h2235, h2237, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h1475, hc01, hc14, hlam, hphi, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h0, h2121, h2238, hc01, hc12, hlam, hphi, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2237, h2239, h2245, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2246_1, u3ehi4]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            rcases p2246_3 (m.d 0 4) (by simp) with h2256 | h2256
                            · linarith only [h1475, h2256, hlam]
                            · linarith only [h2236, h2256, hlam]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2235, h2245, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2246_1, u3ehi4]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2238, hlam, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2237, h2242, h2245, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2246_1, u3ehi4]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2237, h2242, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2235, hlam, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2239, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2242, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2121, h2235, h2237, h2242, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2246_1]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2236, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2241, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2244, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [h2245, hlam, p2246_0]
                          · have p2246_0 := h2246c.1
                            have p2246_1 := h2246c.2.1
                            have p2246_2 := h2246c.2.2.1
                            have p2246_3 := h2246c.2.2.2
                            linarith only [hlam, p2246_0]
                        · linarith only [h2121, h2236, h2237, h2242, h2245, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2121, h2236, h2244, hlam]
                    · linarith only [h1778, h2235, h2243, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1778, h2235, h2242, hlam]
                · linarith only [h1475, h2121, h2236, h2241, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h1314, h2235, h2240, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1778, h2235, h2237, h2239, hlam]
          · linarith only [h1778, h2235, h2237, h2238, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2282 | h2282
          · linarith only [h0, h2121, h2237, h2282, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2284 | h2284
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2285 | h2285
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2286 | h2286
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2287 | h2287
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2288 | h2288
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2289 | h2289
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2290 | h2290
                        · rcases h4bigk with h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h1475, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2121, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2290, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2291_1, u3ehi4]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            rcases p2291_3 (m.d 0 4) (by simp) with h2296 | h2296
                            · rcases p2291_3 (m.d 1 4) (by simp) with h2297 | h2297
                              · rcases p2291_3 (m.d 2 4) (by simp) with h2298 | h2298
                                · rcases p2291_3 (m.d 3 4) (by simp) with h2299 | h2299
                                  · linarith only [h2235, h2299, hlam]
                                  · linarith only [h2290, h2299, hlam]
                                · linarith only [h2289, h2298, hlam]
                              · linarith only [h2286, h2297, hlam]
                            · linarith only [h2296, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h1475, hc01, hc14, hlam, hphi, p2291_1]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2282, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2282, h2287, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2291_1, u3ehi4]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            rcases p2291_3 (m.d 0 4) (by simp) with h2309 | h2309
                            · linarith only [h1475, h2309, hlam]
                            · linarith only [h2236, h2309, hlam]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2235, h2287, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2291_1, u3ehi4]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h1475, h2287, hc01, hc23, hlam, hphi, ht12, p2291_1]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2287, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2291_1, u3ehi4]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            rcases p2291_3 (m.d 0 4) (by simp) with h2316 | h2316
                            · linarith only [h2121, h2316, hlam]
                            · linarith only [h2236, h2316, hlam]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2235, hlam, p2291_1]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2284, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2287, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2235, hc03, hc45, hlam, hphi, ht0b, ht5b, p2291_1]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2236, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2286, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2289, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [h2290, hlam, p2291_0]
                          · have p2291_0 := h2291c.1
                            have p2291_1 := h2291c.2.1
                            have p2291_2 := h2291c.2.2.1
                            have p2291_3 := h2291c.2.2.2
                            linarith only [hlam, p2291_0]
                        · rcases h4bigk with h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h1475, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2121, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h1314, h2235, h2237, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h1314, h2235, h2237, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h1475, h2282, h2287, hc01, hc23, hlam, hphi, ht12, p2329_1]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2282, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2282, h2287, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2282, h2287, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2236, h2287, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h1475, h2287, hc01, hc23, hlam, hphi, ht12, p2329_1]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2287, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2287, h2290, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2235, hlam, p2329_1]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2284, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2287, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2290, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2236, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2286, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2289, hlam, p2329_0]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [h2236, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2329_1, u3ehi3]
                          · have p2329_0 := h2329c.1
                            have p2329_1 := h2329c.2.1
                            have p2329_2 := h2329c.2.2.1
                            have p2329_3 := h2329c.2.2.2
                            linarith only [hlam, p2329_0]
                      · linarith only [h1314, h2235, h2236, h2237, h2282, h2289, hc12, hc23, hlam, hphi]
                    · linarith only [h1314, h2235, h2237, h2288, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h2235, h2237, h2287, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h1475, h2236, h2286, hlam]
              · linarith only [h1314, h2235, h2285, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1314, h2235, h2284, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2361 | h2361
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2362 | h2362
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2363 | h2363
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2364 | h2364
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2365 | h2365
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2366 | h2366
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2367 | h2367
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2368 | h2368
                      · linarith only [h1475, h2236, h2362, h2368, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2121, h2361, h2363, h2365, h2368, hc01, hc12, hlam, hphi]
                    · linarith only [h1778, h2235, h2367, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1778, h2235, h2366, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2373 | h2373
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2374 | h2374
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2375 | h2375
                      · linarith only [h1475, h2365, h2375, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2377 | h2377
                        · linarith only [h0, h2121, h2235, h2362, h2365, h2377, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h4bigk with h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h1475, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2121, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2121, h2362, h2365, hc34, hc45, hlam, hphi, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2236, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2365, hc04, hc45, hlam, hphi, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2365, hc24, hc45, hlam, hphi, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2365, hc45, hlam, hphi, ht34, p2379_1, u3ehi3]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2365, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2235, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2379_1, u3ehi3]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2362, hlam, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2362, h2365, hc45, hlam, hphi, ht34, p2379_1, u3ehi3]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2375, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2235, hlam, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2363, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2373, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2377, hlam, p2379_0]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h2235, hc45, hlam, hphi, ht34, p2379_1, u3ehi3]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hc14, hc45, hlam, hphi, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [h0, h2121, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2379_1]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p2379_1, u3ehi3]
                          · have p2379_0 := h2379c.1
                            have p2379_1 := h2379c.2.1
                            have p2379_2 := h2379c.2.2.1
                            have p2379_3 := h2379c.2.2.2
                            linarith only [hlam, p2379_0]
                    · linarith only [h1778, h2235, h2374, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1778, h2235, h2373, hlam]
              · linarith only [h1314, h2235, h2364, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1778, h2235, h2361, h2363, hlam]
          · linarith only [h1778, h2235, h2361, h2362, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2410 | h2410
          · linarith only [h0, h2121, h2361, h2410, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2412 | h2412
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2413 | h2413
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2414 | h2414
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2415 | h2415
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2416 | h2416
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2417 | h2417
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2418 | h2418
                        · linarith only [h2235, h2236, h2418, hlam]
                        · rcases h4bigk with h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h1475, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2121, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2236, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h1475, h2412, hc01, hc13, hlam, hphi, p2420_1]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2410, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2361, h2412, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2361, h2412, h2418, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2420_1, u3ehi4]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2235, h2415, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h1475, h2415, hc01, hc23, hlam, hphi, ht12, p2420_1]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2415, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2235, h2236, h2415, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2235, hlam, p2420_1]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2412, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2415, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2418, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2235, h2414, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2414, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2417, hlam, p2420_0]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [h2410, h2414, h2415, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2420_1, u3ehi3]
                          · have p2420_0 := h2420c.1
                            have p2420_1 := h2420c.2.1
                            have p2420_2 := h2420c.2.2.1
                            have p2420_3 := h2420c.2.2.2
                            linarith only [hlam, p2420_0]
                      · linarith only [h2410, h2414, h2417, hlam]
                    · linarith only [h1314, h2235, h2361, h2416, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2235, h2236, h2361, h2412, h2414, h2415, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2449 | h2449
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2450 | h2450
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2451 | h2451
                      · linarith only [h0, h2410, h2414, h2449, h2451, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h2410, h2451, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h2361, h2413, h2450, hlam]
                  · linarith only [h2235, h2361, h2413, h2449, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h1314, h2235, h2413, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1314, h2235, h2412, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2458 | h2458
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2459 | h2459
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2460 | h2460
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2461 | h2461
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2462 | h2462
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2463 | h2463
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2464 | h2464
                  · linarith only [h2235, h2459, h2464, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h0, h1778, h2461, h2464, hc01, hc13, hlam, hphi]
                · linarith only [h1475, h2458, h2463, hlam]
              · linarith only [h2235, h2461, h2462, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2469 | h2469
              · linarith only [h2461, h2469, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2471 | h2471
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2472 | h2472
                  · linarith only [h1314, h2461, h2472, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2474 | h2474
                    · linarith only [h2459, h2469, h2474, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2476 | h2476
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2477 | h2477
                        · rcases h4bigk with h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c | h2478c
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h1475, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2121, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2235, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2121, h2460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h1475, hc01, hc14, hlam, hphi, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h0, h2121, h2460, hc01, hc12, hlam, hphi, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2461, hlam, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            rcases p2478_3 (m.d 0 4) (by simp) with h2488 | h2488
                            · linarith only [h1475, h2488, hlam]
                            · linarith only [h2458, h2488, hlam]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2235, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2478_1, u3ehi0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2460, hlam, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2472, hlam, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2235, hc34, hlam, hphi, p2478_1, u3ehi0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h1475, hc01, hc34, hlam, hphi, ht12, ht23, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h0, h2121, hc01, hc34, hlam, hphi, ht12, ht23, p2478_1]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            rcases p2478_3 (m.d 0 4) (by simp) with h2500 | h2500
                            · linarith only [h2235, h2500, hlam]
                            · linarith only [h2458, h2500, hlam]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2458, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2471, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2476, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [h2477, hlam, p2478_0]
                          · have p2478_0 := h2478c.1
                            have p2478_1 := h2478c.2.1
                            have p2478_2 := h2478c.2.2.1
                            have p2478_3 := h2478c.2.2.2
                            linarith only [hlam, p2478_0]
                        · linarith only [h2235, h2477, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h1475, h2121, h2458, h2476, hc01, hc14, hlam, hphi]
                · linarith only [h1475, h2458, h2471, hlam]
          · linarith only [h0, h1778, h2459, h2460, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2512 | h2512
          · linarith only [h0, h2121, h2459, h2512, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2514 | h2514
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2515 | h2515
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2516 | h2516
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2517 | h2517
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2518 | h2518
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2519 | h2519
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2520 | h2520
                        · rcases h4bigk with h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h1475, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2121, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2235, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2235, h2459, h2514, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2521_1]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h1475, h2459, h2514, hc01, hc23, hlam, hphi, ht12, p2521_1]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2512, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2235, h2459, h2514, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2521_1, u3ehi0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            rcases p2521_3 (m.d 0 4) (by simp) with h2531 | h2531
                            · linarith only [h1475, h2531, hlam]
                            · linarith only [h2458, h2531, hlam]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2235, h2517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2521_1, u3ehi0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h1475, h2517, hc01, hc23, hlam, hphi, ht12, p2521_1]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2235, h2517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2521_1, u3ehi0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            rcases p2521_3 (m.d 0 4) (by simp) with h2538 | h2538
                            · linarith only [h2121, h2538, hlam]
                            · linarith only [h2458, h2538, hlam]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2235, h2514, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2521_1, u3ehi0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2514, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2517, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2459, h2514, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2521_1]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2458, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2516, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2519, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [h2520, hlam, p2521_0]
                          · have p2521_0 := h2521c.1
                            have p2521_1 := h2521c.2.1
                            have p2521_2 := h2521c.2.2.1
                            have p2521_3 := h2521c.2.2.2
                            linarith only [hlam, p2521_0]
                        · linarith only [h2235, h2520, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h1475, h2458, h2512, h2519, hlam]
                    · linarith only [h2235, h2459, h2514, h2515, h2518, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h2459, h2514, h2517, hlam]
                · linarith only [h1475, h2458, h2516, hlam]
              · linarith only [h2235, h2514, h2515, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2557 | h2557
              · linarith only [h2514, h2557, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2559 | h2559
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2560 | h2560
                  · linarith only [h0, h2459, h2514, h2560, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2459, h2560, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1475, h2458, h2559, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2564 | h2564
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2565 | h2565
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2566 | h2566
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2567 | h2567
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2568 | h2568
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2569 | h2569
                  · linarith only [h2235, h2564, h2569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h0, h1778, h2564, h2566, h2569, hc01, hc12, hlam, hphi]
                · linarith only [h2235, h2566, h2568, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2235, h2566, h2567, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2574 | h2574
              · linarith only [h2566, h2574, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2576 | h2576
                · linarith only [h2235, h2458, h2566, h2576, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2578 | h2578
                  · linarith only [h2564, h2566, h2576, h2578, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2580 | h2580
                    · linarith only [h2564, h2566, h2576, h2580, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2582 | h2582
                      · linarith only [h0, h1778, h2564, h2566, h2576, h2582, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2584 | h2584
                        · linarith only [h0, h1778, h2564, h2566, h2576, h2584, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h2235, h2584, hc45, hlam, hphi, ht34, u3ehi0]
          · linarith only [h0, h1778, h2564, h2565, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2588 | h2588
          · linarith only [h0, h2121, h2564, h2588, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2590 | h2590
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2591 | h2591
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2592 | h2592
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2593 | h2593
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2594 | h2594
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2595 | h2595
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2596 | h2596
                        · linarith only [h2235, h2458, h2596, hc34, hlam, hphi, u3ehi0]
                        · linarith only [h2235, h2590, h2592, h2596, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h2564, h2588, h2590, h2592, h2595, hc12, hc23, hlam, hphi]
                    · linarith only [h2564, h2591, h2594, hlam]
                  · linarith only [h2564, h2591, h2593, hc34, hlam, hphi, u3ehi4]
                · linarith only [h2235, h2590, h2592, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2235, h2590, h2591, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2604 | h2604
              · linarith only [h2590, h2604, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2606 | h2606
                · linarith only [h2235, h2458, h2590, h2606, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2608 | h2608
                  · linarith only [h0, h2564, h2590, h2608, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2564, h2608, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1475 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1633 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1778 | h1778
  · exact r1l7_13_24_L_R_H_I_x1_x1_x1_x1_x0 m hb3 hb4 h0 h1314 h1475 h1633 h1778
  · exact r1l7_13_24_L_R_H_I_x1_x1_x1_x1_x1 m hb3 hb4 h0 h1314 h1475 h1633 h1778

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1475 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1633 | h1633
  · exact r1l7_13_24_L_R_H_I_x1_x1_x1_x0 m hb3 hb4 h0 h1314 h1475 h1633
  · exact r1l7_13_24_L_R_H_I_x1_x1_x1_x1 m hb3 hb4 h0 h1314 h1475 h1633

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1475 | h1475
  · exact r1l7_13_24_L_R_H_I_x1_x1_x0 m hb3 hb4 h0 h1314 h1475
  · exact r1l7_13_24_L_R_H_I_x1_x1_x1 m hb3 hb4 h0 h1314 h1475

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1314 | h1314
  · exact r1l7_13_24_L_R_H_I_x1_x0 m hb3 hb4 h0 h1314
  · exact r1l7_13_24_L_R_H_I_x1_x1 m hb3 hb4 h0 h1314

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_13_24_L_R_H_I_x0 m hb3 hb4 h0
  · exact r1l7_13_24_L_R_H_I_x1 m hb3 hb4 h0

end R2N4
