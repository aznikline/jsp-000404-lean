import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S2
import Jsp000404.R1LeavesN7_1S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1382 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1543 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1657 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h2118 | h2118
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2119 | h2119
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2120 | h2120
      · linarith only [h0, h1657, h2118, h2120, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2122 | h2122
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2123 | h2123
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2124 | h2124
            · rcases h0bigk with h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h1543, h2122, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h1543, h2120, h2122, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h1543, h2120, h2122, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                rcases p2125_3 (m.d 0 1) (by simp) with h2130 | h2130
                · rcases p2125_3 (m.d 0 2) (by simp) with h2131 | h2131
                  · linarith only [h0, h2131, hlam]
                  · linarith only [h2131, h6, hlam]
                · linarith only [h2130, h3, hlam]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h0, hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h1543, h2120, h2122, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h0, h1543, h2120, h2122, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                rcases p2125_3 (m.d 0 1) (by simp) with h2139 | h2139
                · rcases p2125_3 (m.d 0 2) (by simp) with h2140 | h2140
                  · rcases p2125_3 (m.d 0 3) (by simp) with h2141 | h2141
                    · linarith only [h2141, h4, hlam]
                    · linarith only [h2141, h8, hlam]
                  · linarith only [h2140, h6, hlam]
                · linarith only [h2139, h3, hlam]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h1, hlam, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h4, hlam, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h1543, h2120, h2122, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                rcases p2125_3 (m.d 0 1) (by simp) with h2150 | h2150
                · rcases p2125_3 (m.d 0 2) (by simp) with h2151 | h2151
                  · rcases p2125_3 (m.d 0 3) (by simp) with h2152 | h2152
                    · rcases p2125_3 (m.d 0 4) (by simp) with h2153 | h2153
                      · linarith only [h2153, h7, hlam]
                      · linarith only [h2153, h9, hlam]
                    · linarith only [h2152, h8, hlam]
                  · linarith only [h2151, h6, hlam]
                · linarith only [h2150, h3, hlam]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h2, hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h5, hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h7, hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                rcases p2125_3 (m.d 0 1) (by simp) with h2163 | h2163
                · rcases p2125_3 (m.d 0 2) (by simp) with h2164 | h2164
                  · rcases p2125_3 (m.d 0 3) (by simp) with h2165 | h2165
                    · rcases p2125_3 (m.d 0 4) (by simp) with h2166 | h2166
                      · rcases p2125_3 (m.d 0 5) (by simp) with h2167 | h2167
                        · linarith only [h2167, h9, hlam]
                        · rcases h2bigk with h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h1543, h5, h6, hlam, p2125_1, p2169_2]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            rcases p2169_3 (m.d 0 2) (by simp) with h2172 | h2172
                            · rcases p2169_3 (m.d 1 2) (by simp) with h2173 | h2173
                              · linarith only [h0, h2173, hlam]
                              · rcases p2169_3 (m.d 2 3) (by simp) with h2175 | h2175
                                · linarith only [h2175, hlam, p2169_0]
                                · rcases p2169_3 (m.d 2 4) (by simp) with h2177 | h2177
                                  · linarith only [h2177, h5, hlam]
                                  · linarith only [h2120, h2177, hlam]
                            · linarith only [h2172, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            rcases p2169_3 (m.d 0 2) (by simp) with h2181 | h2181
                            · rcases p2169_3 (m.d 1 2) (by simp) with h2182 | h2182
                              · linarith only [h0, h2182, hlam]
                              · rcases p2169_3 (m.d 2 3) (by simp) with h2184 | h2184
                                · linarith only [h2184, h4, hlam]
                                · rcases p2169_3 (m.d 2 4) (by simp) with h2186 | h2186
                                  · linarith only [h2186, hlam, p2169_0]
                                  · rcases p2169_3 (m.d 2 5) (by simp) with h2188 | h2188
                                    · linarith only [h2188, h6, hlam]
                                    · rcases h3bigk with h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        rcases p2190_3 (m.d 0 3) (by simp) with h2192 | h2192
                                        · rcases p2190_3 (m.d 1 3) (by simp) with h2193 | h2193
                                          · linarith only [h1, h2193, hlam]
                                          · rcases p2190_3 (m.d 2 3) (by simp) with h2195 | h2195
                                            · linarith only [h2195, h4, hlam]
                                            · linarith only [h10, h2195, hlam]
                                        · linarith only [h1, h2192, hlam]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        rcases p2190_3 (m.d 0 3) (by simp) with h2199 | h2199
                                        · rcases p2190_3 (m.d 1 3) (by simp) with h2200 | h2200
                                          · linarith only [h1, h2200, hlam]
                                          · rcases p2190_3 (m.d 2 3) (by simp) with h2202 | h2202
                                            · linarith only [h2202, h4, hlam]
                                            · rcases p2190_3 (m.d 3 4) (by simp) with h2204 | h2204
                                              · linarith only [h2204, h7, hlam]
                                              · linarith only [h2120, h2204, hlam]
                                        · linarith only [h2199, h4, hlam]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h1543, h2120, h2122, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h10, h2118, h2120, h7, hlam, p2190_2]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h1, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h10, hlam, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h1657, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h10, h2120, h7, hc03, hc35, hlam, hphi, ht0b, ht5b, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h4, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h2120, h7, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h2120, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h0, h2120, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h7, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h0, h2118, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2190_1]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        rcases p2190_3 (m.d 0 3) (by simp) with h2224 | h2224
                                        · rcases p2190_3 (m.d 1 3) (by simp) with h2225 | h2225
                                          · linarith only [h1657, h2225, hlam]
                                          · linarith only [h2118, h2225, hlam]
                                        · linarith only [h2224, h8, hlam]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h8, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h2118, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h2122, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [h2124, hlam, p2190_0]
                                      · have p2190_0 := h2190c.1
                                        have p2190_1 := h2190c.2.1
                                        have p2190_2 := h2190c.2.2.1
                                        have p2190_3 := h2190c.2.2.2
                                        linarith only [hlam, p2190_0]
                            · linarith only [h2181, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            rcases p2169_3 (m.d 0 2) (by simp) with h2235 | h2235
                            · rcases p2169_3 (m.d 1 2) (by simp) with h2236 | h2236
                              · linarith only [h0, h2236, hlam]
                              · rcases p2169_3 (m.d 2 3) (by simp) with h2238 | h2238
                                · linarith only [h2238, h4, hlam]
                                · linarith only [h2122, h2238, hlam]
                            · linarith only [h2235, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h0, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h10, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h1382, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h1543, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h4, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h0, h2120, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2169_1]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h2120, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h0, h1543, h2120, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2169_1]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h5, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            rcases p2169_3 (m.d 0 2) (by simp) with h2253 | h2253
                            · rcases p2169_3 (m.d 1 2) (by simp) with h2254 | h2254
                              · linarith only [h2254, hlam, p2169_0]
                              · rcases p2169_3 (m.d 2 3) (by simp) with h2256 | h2256
                                · linarith only [h2120, h2256, hlam]
                                · linarith only [h10, h2256, hlam]
                            · linarith only [h0, h2253, hlam]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h10, hc12, hc24, hlam, hphi, p2169_1]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h0, h1543, h2120, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2169_1]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h6, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1, p2169_1]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h2122, hlam, p2169_1]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [h2123, hlam, p2169_0]
                          · have p2169_0 := h2169c.1
                            have p2169_1 := h2169c.2.1
                            have p2169_2 := h2169c.2.2.1
                            have p2169_3 := h2169c.2.2.2
                            linarith only [hlam, p2169_0]
                      · linarith only [h2166, h9, hlam]
                    · linarith only [h2165, h8, hlam]
                  · linarith only [h2164, h6, hlam]
                · linarith only [h2163, h3, hlam]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h3, hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h6, hlam, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h8, hlam, p2125_0]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [h9, hlam, p2125_1]
              · have p2125_0 := h2125c.1
                have p2125_1 := h2125c.2.1
                have p2125_2 := h2125c.2.2.1
                have p2125_3 := h2125c.2.2.2
                linarith only [hlam, p2125_0]
            · linarith only [h0, h10, h2120, h2124, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1382, h1543, h2119, h2120, h2122, h2123, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h10, h2118, h2122, hlam]
    · linarith only [h1657, h2118, h2119, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2281 | h2281
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2282 | h2282
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2283 | h2283
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2284 | h2284
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2285 | h2285
            · rcases h0bigk with h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h2118, h2282, h2285, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h2118, h2282, h2285, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2290 | h2290
                · rcases p2286_3 (m.d 0 2) (by simp) with h2291 | h2291
                  · linarith only [h0, h2291, hlam]
                  · linarith only [h2291, h5, hlam]
                · linarith only [h2, h2290, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2295 | h2295
                · rcases p2286_3 (m.d 0 2) (by simp) with h2296 | h2296
                  · linarith only [h0, h2296, hlam]
                  · linarith only [h2296, h6, hlam]
                · linarith only [h2295, h3, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h0, hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h10, h2118, h2282, h2285, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2303 | h2303
                · rcases p2286_3 (m.d 0 2) (by simp) with h2304 | h2304
                  · rcases p2286_3 (m.d 0 3) (by simp) with h2305 | h2305
                    · linarith only [h2305, h4, hlam]
                    · linarith only [h2305, h7, hlam]
                  · linarith only [h2304, h5, hlam]
                · linarith only [h2, h2303, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2310 | h2310
                · rcases p2286_3 (m.d 0 2) (by simp) with h2311 | h2311
                  · rcases p2286_3 (m.d 0 3) (by simp) with h2312 | h2312
                    · linarith only [h2312, h4, hlam]
                    · linarith only [h2312, h8, hlam]
                  · linarith only [h2311, h6, hlam]
                · linarith only [h2310, h3, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h1, hlam, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h4, hlam, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2320 | h2320
                · rcases p2286_3 (m.d 0 2) (by simp) with h2321 | h2321
                  · rcases p2286_3 (m.d 0 3) (by simp) with h2322 | h2322
                    · rcases p2286_3 (m.d 0 4) (by simp) with h2323 | h2323
                      · linarith only [h2323, h7, hlam]
                      · rcases p2286_3 (m.d 0 5) (by simp) with h2325 | h2325
                        · linarith only [h2325, h8, hlam]
                        · rcases h2bigk with h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c | h2327c
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h10, h2118, h2282, h2285, h4, hlam, p2327_2]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h10, h2118, h2282, h2285, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            rcases p2327_3 (m.d 0 2) (by simp) with h2331 | h2331
                            · rcases p2327_3 (m.d 1 2) (by simp) with h2332 | h2332
                              · linarith only [h0, h2332, hlam]
                              · rcases p2327_3 (m.d 2 3) (by simp) with h2334 | h2334
                                · linarith only [h2334, h4, hlam]
                                · linarith only [h2282, h2334, hlam]
                            · linarith only [h2331, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            rcases p2327_3 (m.d 0 2) (by simp) with h2338 | h2338
                            · rcases p2327_3 (m.d 1 2) (by simp) with h2339 | h2339
                              · linarith only [h0, h2339, hlam]
                              · rcases p2327_3 (m.d 2 3) (by simp) with h2341 | h2341
                                · linarith only [h2341, h4, hlam]
                                · linarith only [h2283, h2341, hlam]
                            · linarith only [h2338, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h0, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h10, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h1382, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h1543, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h4, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            rcases p2327_3 (m.d 0 2) (by simp) with h2351 | h2351
                            · rcases p2327_3 (m.d 1 2) (by simp) with h2352 | h2352
                              · linarith only [h2352, hlam, p2327_0]
                              · rcases p2327_3 (m.d 2 3) (by simp) with h2354 | h2354
                                · rcases p2327_3 (m.d 2 4) (by simp) with h2355 | h2355
                                  · linarith only [h2282, h2355, hlam]
                                  · linarith only [h1382, h2355, hlam]
                                · linarith only [h2354, hlam, p2327_0]
                            · linarith only [h0, h2351, hlam]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h10, h2118, h2283, h2284, hc12, hc23, hlam, hphi, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h0, h10, h2118, h2283, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h5, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h0, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2286_1, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h2282, hlam, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h0, h10, h2118, h2283, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2286_1, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h6, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2286_1, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h2283, hlam, p2327_1]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [h2284, hlam, p2327_0]
                          · have p2327_0 := h2327c.1
                            have p2327_1 := h2327c.2.1
                            have p2327_2 := h2327c.2.2.1
                            have p2327_3 := h2327c.2.2.2
                            linarith only [hlam, p2327_0]
                    · linarith only [h2322, h7, hlam]
                  · linarith only [h2321, h5, hlam]
                · linarith only [h2, h2320, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2376 | h2376
                · rcases p2286_3 (m.d 0 2) (by simp) with h2377 | h2377
                  · rcases p2286_3 (m.d 0 3) (by simp) with h2378 | h2378
                    · rcases p2286_3 (m.d 0 4) (by simp) with h2379 | h2379
                      · linarith only [h2379, h7, hlam]
                      · linarith only [h2379, h9, hlam]
                    · linarith only [h2378, h8, hlam]
                  · linarith only [h2377, h6, hlam]
                · linarith only [h2376, h3, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h2, hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h5, hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h7, hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                rcases p2286_3 (m.d 0 1) (by simp) with h2389 | h2389
                · rcases p2286_3 (m.d 0 2) (by simp) with h2390 | h2390
                  · rcases p2286_3 (m.d 0 3) (by simp) with h2391 | h2391
                    · rcases p2286_3 (m.d 0 4) (by simp) with h2392 | h2392
                      · rcases p2286_3 (m.d 0 5) (by simp) with h2393 | h2393
                        · linarith only [h2393, h9, hlam]
                        · rcases h2bigk with h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h10, h2118, h4, h7, h8, hlam, p2286_1, p2395_2]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h0, h10, h2118, h2282, h2285, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            rcases p2395_3 (m.d 0 2) (by simp) with h2399 | h2399
                            · rcases p2395_3 (m.d 1 2) (by simp) with h2400 | h2400
                              · linarith only [h0, h2400, hlam]
                              · rcases p2395_3 (m.d 2 3) (by simp) with h2402 | h2402
                                · linarith only [h2402, h4, hlam]
                                · linarith only [h2282, h2402, hlam]
                            · linarith only [h2399, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            rcases p2395_3 (m.d 0 2) (by simp) with h2406 | h2406
                            · rcases p2395_3 (m.d 1 2) (by simp) with h2407 | h2407
                              · linarith only [h0, h2407, hlam]
                              · rcases p2395_3 (m.d 2 3) (by simp) with h2409 | h2409
                                · linarith only [h2409, h4, hlam]
                                · linarith only [h2283, h2409, hlam]
                            · linarith only [h2406, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h0, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h10, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h1382, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h1543, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h4, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            rcases p2395_3 (m.d 0 2) (by simp) with h2419 | h2419
                            · rcases p2395_3 (m.d 1 2) (by simp) with h2420 | h2420
                              · linarith only [h2420, hlam, p2395_0]
                              · rcases p2395_3 (m.d 2 3) (by simp) with h2422 | h2422
                                · rcases p2395_3 (m.d 2 4) (by simp) with h2423 | h2423
                                  · linarith only [h2282, h2423, hlam]
                                  · linarith only [h1382, h2423, hlam]
                                · linarith only [h2422, hlam, p2395_0]
                            · linarith only [h0, h2419, hlam]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h1382, hc12, hc23, hlam, hphi, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h0, h1543, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h5, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            rcases p2395_3 (m.d 0 2) (by simp) with h2432 | h2432
                            · rcases p2395_3 (m.d 1 2) (by simp) with h2433 | h2433
                              · linarith only [h2433, hlam, p2395_0]
                              · rcases p2395_3 (m.d 2 3) (by simp) with h2435 | h2435
                                · rcases p2395_3 (m.d 2 4) (by simp) with h2436 | h2436
                                  · rcases p2395_3 (m.d 2 5) (by simp) with h2437 | h2437
                                    · linarith only [h2284, h2437, hlam]
                                    · linarith only [h1543, h2437, hlam]
                                  · linarith only [h2436, hlam, p2395_0]
                                · linarith only [h10, h2435, hlam]
                            · linarith only [h0, h2432, hlam]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h2282, hlam, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h10, h2118, h2283, hc12, hc24, hlam, hphi, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h6, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2286_1, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h2283, hlam, p2395_1]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [h2284, hlam, p2395_0]
                          · have p2395_0 := h2395c.1
                            have p2395_1 := h2395c.2.1
                            have p2395_2 := h2395c.2.2.1
                            have p2395_3 := h2395c.2.2.2
                            linarith only [hlam, p2395_0]
                      · linarith only [h2392, h9, hlam]
                    · linarith only [h2391, h8, hlam]
                  · linarith only [h2390, h6, hlam]
                · linarith only [h2389, h3, hlam]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h3, hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h6, hlam, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h8, hlam, p2286_0]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [h9, hlam, p2286_1]
              · have p2286_0 := h2286c.1
                have p2286_1 := h2286c.2.1
                have p2286_2 := h2286c.2.2.1
                have p2286_3 := h2286c.2.2.2
                linarith only [hlam, p2286_0]
            · linarith only [h10, h1657, h2, h2281, h2285, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1382, h2281, h2284, hlam]
        · linarith only [h0, h10, h1657, h2282, h2283, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2463 | h2463
        · linarith only [h10, h2118, h2282, h2463, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2465 | h2465
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2466 | h2466
            · rcases h0bigk with h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h10, h2463, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h10, h2463, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h10, h2463, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h0, hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h10, h2463, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h0, h10, h2463, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h0, h10, h2463, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h1, hlam, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h4, hlam, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h0, h10, h2463, h4, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h0, h10, h2463, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h2, hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h5, hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h7, hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h10, h2463, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h3, hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h6, hlam, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h8, hlam, p2467_0]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [h9, hlam, p2467_1]
              · have p2467_0 := h2467c.1
                have p2467_1 := h2467c.2.1
                have p2467_2 := h2467c.2.2.1
                have p2467_3 := h2467c.2.2.2
                linarith only [hlam, p2467_0]
            · linarith only [h1382, h2281, h2282, h2466, hlam]
          · linarith only [h1382, h2281, h2465, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2495 | h2495
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2496 | h2496
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2497 | h2497
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2498 | h2498
            · linarith only [h0, h2281, h2495, h2498, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1657, h2495, h2497, h2498, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2501 | h2501
            · linarith only [h0, h1382, h2497, h2501, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h0bigk with h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h2496, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h10, h1657, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h10, h1657, h2495, h2497, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h10, h1657, h2495, h2497, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h0, hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h10, h1657, h2495, h2497, h8, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h0, h10, h1657, h2495, h2497, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h0, h10, h1657, h2495, h2497, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h1, hlam, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h4, hlam, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h10, h1657, h2495, h2497, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h0, h10, h1657, h2495, h2497, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h2, hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h5, hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h7, hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h10, h1657, h2495, h2497, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h3, hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h6, hlam, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h8, hlam, p2503_0]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [h9, hlam, p2503_1]
              · have p2503_0 := h2503c.1
                have p2503_1 := h2503c.2.1
                have p2503_2 := h2503c.2.2.1
                have p2503_3 := h2503c.2.2.2
                linarith only [hlam, p2503_0]
        · linarith only [h10, h1657, h2495, h2496, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2530 | h2530
        · linarith only [h0, h10, h2118, h2495, h2530, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2532 | h2532
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2533 | h2533
            · rcases h0bigk with h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h2530, h2533, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h2530, h2533, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h10, h2530, h2533, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h10, h2530, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h0, hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h10, h2530, h2533, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h0, h10, h2530, h2533, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h0, h10, h2530, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h1, hlam, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h4, hlam, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h0, h10, h2530, h2533, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h0, h10, h2530, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h2, hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h5, hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h7, hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h10, h2530, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h3, hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h6, hlam, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h8, hlam, p2534_0]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [h9, hlam, p2534_1]
              · have p2534_0 := h2534c.1
                have p2534_1 := h2534c.2.1
                have p2534_2 := h2534c.2.2.1
                have p2534_3 := h2534c.2.2.2
                linarith only [hlam, p2534_0]
            · linarith only [h2495, h2532, h2533, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2561 | h2561
            · linarith only [h0, h1382, h2532, h2561, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h10, h2495, h2561, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1382 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1543 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h1657 | h1657
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1382 h1543 h1657
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1382 h1543 h1657

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1382 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h1543 | h1543
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1382 h1543
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1382 h1543

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 4 (by decide) (by decide) with h1382 | h1382
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1382
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1382

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10

set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

end R2N4
