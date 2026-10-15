import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S2
import Jsp000404.R1LeavesN7_18S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1617 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h1790 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h2071 | h2071
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2072 | h2072
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2073 | h2073
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2074 | h2074
        · linarith only [h1, h2074, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2076 | h2076
          · linarith only [h1, h1617, h2076, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2078 | h2078
            · linarith only [h1, h2071, h2078, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2080 | h2080
              · linarith only [h1, h1617, h2071, h2080, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2082 | h2082
                · linarith only [h0, h1790, h2072, h2082, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2084 | h2084
                  · rcases h0bigk with h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h0, h2073, hc01, hc25, hlam, hphi, ht0b, ht5b, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      rcases p2085_3 (m.d 0 1) (by simp) with h2088 | h2088
                      · rcases p2085_3 (m.d 0 2) (by simp) with h2089 | h2089
                        · linarith only [h0, h2089, hlam]
                        · linarith only [h2089, h4, hlam]
                      · linarith only [h1, h2088, hlam]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      rcases p2085_3 (m.d 0 1) (by simp) with h2093 | h2093
                      · rcases p2085_3 (m.d 0 2) (by simp) with h2094 | h2094
                        · linarith only [h0, h2094, hlam]
                        · linarith only [h2094, h5, hlam]
                      · linarith only [h2, h2093, hlam]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      rcases p2085_3 (m.d 0 1) (by simp) with h2098 | h2098
                      · rcases p2085_3 (m.d 0 2) (by simp) with h2099 | h2099
                        · linarith only [h0, h2099, hlam]
                        · linarith only [h2099, h6, hlam]
                      · linarith only [h2098, h3, hlam]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h0, hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      rcases p2085_3 (m.d 0 1) (by simp) with h2105 | h2105
                      · rcases p2085_3 (m.d 0 2) (by simp) with h2106 | h2106
                        · rcases p2085_3 (m.d 0 3) (by simp) with h2107 | h2107
                          · linarith only [h2107, h4, hlam]
                          · rcases p2085_3 (m.d 0 4) (by simp) with h2109 | h2109
                            · linarith only [h2109, h5, hlam]
                            · linarith only [h2109, h7, hlam]
                        · linarith only [h2106, h4, hlam]
                      · linarith only [h1, h2105, hlam]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      rcases p2085_3 (m.d 0 1) (by simp) with h2114 | h2114
                      · rcases p2085_3 (m.d 0 2) (by simp) with h2115 | h2115
                        · rcases p2085_3 (m.d 0 3) (by simp) with h2116 | h2116
                          · linarith only [h2116, h4, hlam]
                          · rcases p2085_3 (m.d 0 4) (by simp) with h2118 | h2118
                            · linarith only [h2118, h5, hlam]
                            · rcases p2085_3 (m.d 0 5) (by simp) with h2120 | h2120
                              · linarith only [h2120, h6, hlam]
                              · linarith only [h1790, h2120, hlam]
                        · linarith only [h2115, h5, hlam]
                      · linarith only [h2, h2114, hlam]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      rcases p2085_3 (m.d 0 1) (by simp) with h2125 | h2125
                      · rcases p2085_3 (m.d 0 2) (by simp) with h2126 | h2126
                        · rcases p2085_3 (m.d 0 3) (by simp) with h2127 | h2127
                          · linarith only [h2127, h4, hlam]
                          · rcases p2085_3 (m.d 0 4) (by simp) with h2129 | h2129
                            · linarith only [h2129, h5, hlam]
                            · rcases p2085_3 (m.d 0 5) (by simp) with h2131 | h2131
                              · linarith only [h2131, h6, hlam]
                              · rcases h2bigk with h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c | h2133c
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  rcases p2133_3 (m.d 0 2) (by simp) with h2135 | h2135
                                  · rcases p2133_3 (m.d 1 2) (by simp) with h2136 | h2136
                                    · linarith only [h0, h2136, hlam]
                                    · rcases p2133_3 (m.d 2 3) (by simp) with h2138 | h2138
                                      · linarith only [h2138, h4, hlam]
                                      · rcases p2133_3 (m.d 2 4) (by simp) with h2140 | h2140
                                        · linarith only [h2140, h5, hlam]
                                        · rcases p2133_3 (m.d 2 5) (by simp) with h2142 | h2142
                                          · linarith only [h2142, h6, hlam]
                                          · rcases h3bigk with h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c | h2144c
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2071, h7, hc23, hc34, hlam, hphi, p2144_1]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h7, hc23, hc34, hlam, hphi, p2144_1]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h7, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h1617, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h1, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h1, h7, hc23, hc34, hlam, hphi, p2144_1]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2074, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2076, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h4, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2071, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2078, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2080, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              rcases p2144_3 (m.d 0 3) (by simp) with h2160 | h2160
                                              · linarith only [h2160, hlam, p2144_0]
                                              · rcases p2144_3 (m.d 1 3) (by simp) with h2162 | h2162
                                                · linarith only [h2074, h2162, hlam]
                                                · rcases p2144_3 (m.d 2 3) (by simp) with h2164 | h2164
                                                  · linarith only [h2078, h2164, hlam]
                                                  · rcases p2144_3 (m.d 3 4) (by simp) with h2166 | h2166
                                                    · rcases p2144_3 (m.d 3 5) (by simp) with h2167 | h2167
                                                      · linarith only [h2084, h2167, hlam]
                                                      · linarith only [h1617, h2167, hlam]
                                                    · linarith only [h2166, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              rcases p2144_3 (m.d 0 3) (by simp) with h2171 | h2171
                                              · linarith only [h2171, h7, hlam]
                                              · linarith only [h1, h2171, hlam]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              rcases p2144_3 (m.d 0 3) (by simp) with h2174 | h2174
                                              · linarith only [h2174, h7, hlam]
                                              · linarith only [h2174, h4, hlam]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h1790, h2084, h7, hc03, hc34, hlam, hphi, p2144_1]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              rcases p2144_3 (m.d 0 3) (by simp) with h2179 | h2179
                                              · linarith only [h2179, hlam, p2144_0]
                                              · rcases p2144_3 (m.d 1 3) (by simp) with h2181 | h2181
                                                · linarith only [h2076, h2181, hlam]
                                                · rcases p2144_3 (m.d 2 3) (by simp) with h2183 | h2183
                                                  · linarith only [h2080, h2183, hlam]
                                                  · rcases p2144_3 (m.d 3 4) (by simp) with h2185 | h2185
                                                    · rcases p2144_3 (m.d 3 5) (by simp) with h2186 | h2186
                                                      · rcases h5bigk with h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [hlam, p2187_0]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h0, h2073, h2078, h2082, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h0, h2078, h2082, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h1617, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h1790, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h3, hlam, p2187_0]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [hlam, p2187_0]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h0, h2078, h2082, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2076, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h0, h1, h1790, h2071, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h6, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2073, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [hlam, p2187_0]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2080, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2082, hlam, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          rcases p2187_3 (m.d 0 5) (by simp) with h2203 | h2203
                                                          · linarith only [h1617, h2203, hlam]
                                                          · rcases p2187_3 (m.d 1 5) (by simp) with h2205 | h2205
                                                            · linarith only [h2076, h2205, hlam]
                                                            · rcases p2187_3 (m.d 2 5) (by simp) with h2207 | h2207
                                                              · linarith only [h2080, h2207, hlam]
                                                              · rcases p2187_3 (m.d 3 5) (by simp) with h2209 | h2209
                                                                · rcases p2187_3 (m.d 4 5) (by simp) with h2210 | h2210
                                                                  · linarith only [h2084, h2210, hlam]
                                                                  · linarith only [h1790, h2210, hlam]
                                                                · linarith only [h1617, h2209, hlam]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          rcases p2187_3 (m.d 0 5) (by simp) with h2214 | h2214
                                                          · linarith only [h1617, h2214, hlam]
                                                          · linarith only [h2214, h3, hlam]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          rcases p2187_3 (m.d 0 5) (by simp) with h2217 | h2217
                                                          · linarith only [h1617, h2217, hlam]
                                                          · linarith only [h2217, h6, hlam]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [hlam, p2187_0]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h1, h1790, h2071, h7, hc23, hc35, hlam, hphi, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2078, h2082, h2084, h6, hc23, hc34, hlam, hphi, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2073, h2078, h2082, h2084, hc23, hc34, hlam, hphi, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2078, h2082, h2084, hc23, hc34, hlam, hphi, p2187_1]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [h2084, hlam, p2187_0]
                                                        · have p2187_0 := h2187c.1
                                                          have p2187_1 := h2187c.2.1
                                                          have p2187_2 := h2187c.2.2.1
                                                          have p2187_3 := h2187c.2.2.2
                                                          linarith only [hlam, p2187_0]
                                                      · linarith only [h2186, hlam, p2144_0]
                                                    · linarith only [h2185, h7, hlam]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              rcases p2144_3 (m.d 0 3) (by simp) with h2229 | h2229
                                              · linarith only [h1617, h2229, hlam]
                                              · linarith only [h1, h2229, hlam]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              rcases p2144_3 (m.d 0 3) (by simp) with h2232 | h2232
                                              · linarith only [h1617, h2232, hlam]
                                              · linarith only [h2232, h4, hlam]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [h2084, hlam, p2144_0]
                                            · have p2144_0 := h2144c.1
                                              have p2144_1 := h2144c.2.1
                                              have p2144_2 := h2144c.2.2.1
                                              have p2144_3 := h2144c.2.2.2
                                              linarith only [hlam, p2144_0]
                                  · linarith only [h0, h2135, hlam]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h1, h1790, h2071, h7, hlam, p2085_1, p2133_2]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2073, h2082, h3, hlam, p2085_1, p2133_2]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2073, h3, hlam, p2085_1, p2133_2]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h0, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  rcases p2133_3 (m.d 0 2) (by simp) with h2243 | h2243
                                  · rcases p2133_3 (m.d 1 2) (by simp) with h2244 | h2244
                                    · rcases p2133_3 (m.d 2 3) (by simp) with h2245 | h2245
                                      · linarith only [h2245, hlam, p2133_0]
                                      · rcases p2133_3 (m.d 2 4) (by simp) with h2247 | h2247
                                        · linarith only [h2072, h2247, hlam]
                                        · linarith only [h2078, h2247, hlam]
                                    · linarith only [h2244, hlam, p2133_0]
                                  · linarith only [h2243, h4, hlam]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  rcases p2133_3 (m.d 0 2) (by simp) with h2252 | h2252
                                  · rcases p2133_3 (m.d 1 2) (by simp) with h2253 | h2253
                                    · rcases p2133_3 (m.d 2 3) (by simp) with h2254 | h2254
                                      · linarith only [h2071, h2254, hlam]
                                      · rcases p2133_3 (m.d 2 4) (by simp) with h2256 | h2256
                                        · linarith only [h2256, hlam, p2133_0]
                                        · rcases p2133_3 (m.d 2 5) (by simp) with h2258 | h2258
                                          · linarith only [h2073, h2258, hlam]
                                          · linarith only [h2082, h2258, hlam]
                                    · linarith only [h2253, hlam, p2133_0]
                                  · linarith only [h2252, h5, hlam]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  rcases p2133_3 (m.d 0 2) (by simp) with h2263 | h2263
                                  · rcases p2133_3 (m.d 1 2) (by simp) with h2264 | h2264
                                    · rcases p2133_3 (m.d 2 3) (by simp) with h2265 | h2265
                                      · linarith only [h2071, h2265, hlam]
                                      · rcases p2133_3 (m.d 2 4) (by simp) with h2267 | h2267
                                        · linarith only [h2072, h2267, hlam]
                                        · rcases p2133_3 (m.d 2 5) (by simp) with h2269 | h2269
                                          · linarith only [h2269, hlam, p2133_0]
                                          · rcases h3bigk with h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h1790, h2071, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2271_1]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h0, h1790, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2271_1]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h7, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h1617, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h1, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h0, h1, h1790, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2271_1]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h2074, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h2076, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h4, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h2071, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h2078, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h2080, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              rcases p2271_3 (m.d 0 3) (by simp) with h2287 | h2287
                                              · linarith only [h2287, hlam, p2271_0]
                                              · rcases p2271_3 (m.d 1 3) (by simp) with h2289 | h2289
                                                · linarith only [h2074, h2289, hlam]
                                                · rcases p2271_3 (m.d 2 3) (by simp) with h2291 | h2291
                                                  · linarith only [h2078, h2291, hlam]
                                                  · rcases p2271_3 (m.d 3 4) (by simp) with h2293 | h2293
                                                    · rcases p2271_3 (m.d 3 5) (by simp) with h2294 | h2294
                                                      · linarith only [h2084, h2294, hlam]
                                                      · linarith only [h1617, h2294, hlam]
                                                    · linarith only [h2293, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              rcases p2271_3 (m.d 0 3) (by simp) with h2298 | h2298
                                              · linarith only [h2298, h7, hlam]
                                              · linarith only [h1, h2298, hlam]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              rcases p2271_3 (m.d 0 3) (by simp) with h2301 | h2301
                                              · linarith only [h2301, h7, hlam]
                                              · linarith only [h2301, h4, hlam]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h1617, hc03, hc34, hlam, hphi, p2271_1]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              rcases p2271_3 (m.d 0 3) (by simp) with h2306 | h2306
                                              · linarith only [h2306, hlam, p2271_0]
                                              · rcases p2271_3 (m.d 1 3) (by simp) with h2308 | h2308
                                                · linarith only [h2076, h2308, hlam]
                                                · rcases p2271_3 (m.d 2 3) (by simp) with h2310 | h2310
                                                  · linarith only [h2080, h2310, hlam]
                                                  · rcases p2271_3 (m.d 3 4) (by simp) with h2312 | h2312
                                                    · rcases p2271_3 (m.d 3 5) (by simp) with h2313 | h2313
                                                      · rcases h5bigk with h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [hlam, p2314_0]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2085_1, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h0, h2082, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2085_1, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h1617, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h1790, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h3, hlam, p2314_0]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [hlam, p2314_0]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h0, h2082, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2085_1, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2076, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2085_1, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h6, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2073, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [hlam, p2314_0]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2080, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2082, hlam, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          rcases p2314_3 (m.d 0 5) (by simp) with h2330 | h2330
                                                          · linarith only [h1617, h2330, hlam]
                                                          · rcases p2314_3 (m.d 1 5) (by simp) with h2332 | h2332
                                                            · linarith only [h2076, h2332, hlam]
                                                            · rcases p2314_3 (m.d 2 5) (by simp) with h2334 | h2334
                                                              · linarith only [h2080, h2334, hlam]
                                                              · rcases p2314_3 (m.d 3 5) (by simp) with h2336 | h2336
                                                                · rcases p2314_3 (m.d 4 5) (by simp) with h2337 | h2337
                                                                  · linarith only [h2084, h2337, hlam]
                                                                  · linarith only [h1790, h2337, hlam]
                                                                · linarith only [h1617, h2336, hlam]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          rcases p2314_3 (m.d 0 5) (by simp) with h2341 | h2341
                                                          · linarith only [h1617, h2341, hlam]
                                                          · linarith only [h2341, h3, hlam]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          rcases p2314_3 (m.d 0 5) (by simp) with h2344 | h2344
                                                          · linarith only [h1617, h2344, hlam]
                                                          · linarith only [h2344, h6, hlam]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [hlam, p2314_0]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h1790, h2078, h5, hc23, hc35, hlam, hphi, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2078, h2082, h2084, h6, hc23, hc34, hlam, hphi, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2073, h2078, h2082, h2084, hc23, hc34, hlam, hphi, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2078, h2082, h2084, hc23, hc34, hlam, hphi, p2314_1]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [h2084, hlam, p2314_0]
                                                        · have p2314_0 := h2314c.1
                                                          have p2314_1 := h2314c.2.1
                                                          have p2314_2 := h2314c.2.2.1
                                                          have p2314_3 := h2314c.2.2.2
                                                          linarith only [hlam, p2314_0]
                                                      · linarith only [h2313, hlam, p2271_0]
                                                    · linarith only [h2312, h7, hlam]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              rcases p2271_3 (m.d 0 3) (by simp) with h2356 | h2356
                                              · linarith only [h1617, h2356, hlam]
                                              · linarith only [h1, h2356, hlam]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              rcases p2271_3 (m.d 0 3) (by simp) with h2359 | h2359
                                              · linarith only [h1617, h2359, hlam]
                                              · linarith only [h2359, h4, hlam]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [h2084, hlam, p2271_0]
                                            · have p2271_0 := h2271c.1
                                              have p2271_1 := h2271c.2.1
                                              have p2271_2 := h2271c.2.2.1
                                              have p2271_3 := h2271c.2.2.2
                                              linarith only [hlam, p2271_0]
                                    · linarith only [h2264, hlam, p2133_0]
                                  · linarith only [h2263, h6, hlam]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h4, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2071, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2078, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2080, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h5, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2072, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h0, h2073, h2082, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2133_1]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2082, hlam, p2133_1]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h6, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h2073, hlam, p2133_0]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h0, h2073, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1, p2133_1]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [h0, h2073, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2085_1, p2133_1]
                                · have p2133_0 := h2133c.1
                                  have p2133_1 := h2133c.2.1
                                  have p2133_2 := h2133c.2.2.1
                                  have p2133_3 := h2133c.2.2.2
                                  linarith only [hlam, p2133_0]
                        · linarith only [h2126, h6, hlam]
                      · linarith only [h2125, h3, hlam]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h1, hlam, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h4, hlam, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h7, hlam, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h1617, hlam, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h2, hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h5, hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h1, h2071, h7, hc23, hc34, hlam, hphi, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h1790, hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h3, hlam, p2085_0]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h6, hlam, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h1, h1617, h2071, h2084, hc23, hc34, hlam, hphi, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [h1790, h2084, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2085_1]
                    · have p2085_0 := h2085c.1
                      have p2085_1 := h2085c.2.1
                      have p2085_2 := h2085c.2.2.1
                      have p2085_3 := h2085c.2.2.2
                      linarith only [hlam, p2085_0]
                  · rcases h0bigk with h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h0, h2073, hc01, hc25, hlam, hphi, ht0b, ht5b, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      rcases p2398_3 (m.d 0 1) (by simp) with h2401 | h2401
                      · rcases p2398_3 (m.d 0 2) (by simp) with h2402 | h2402
                        · linarith only [h0, h2402, hlam]
                        · linarith only [h2402, h4, hlam]
                      · linarith only [h1, h2401, hlam]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      rcases p2398_3 (m.d 0 1) (by simp) with h2406 | h2406
                      · rcases p2398_3 (m.d 0 2) (by simp) with h2407 | h2407
                        · linarith only [h0, h2407, hlam]
                        · linarith only [h2407, h5, hlam]
                      · linarith only [h2, h2406, hlam]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      rcases p2398_3 (m.d 0 1) (by simp) with h2411 | h2411
                      · rcases p2398_3 (m.d 0 2) (by simp) with h2412 | h2412
                        · linarith only [h0, h2412, hlam]
                        · linarith only [h2412, h6, hlam]
                      · linarith only [h2411, h3, hlam]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h0, hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      rcases p2398_3 (m.d 0 1) (by simp) with h2418 | h2418
                      · rcases p2398_3 (m.d 0 2) (by simp) with h2419 | h2419
                        · rcases p2398_3 (m.d 0 3) (by simp) with h2420 | h2420
                          · linarith only [h2420, h4, hlam]
                          · rcases p2398_3 (m.d 0 4) (by simp) with h2422 | h2422
                            · linarith only [h2422, h5, hlam]
                            · linarith only [h2422, h7, hlam]
                        · linarith only [h2419, h4, hlam]
                      · linarith only [h1, h2418, hlam]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      rcases p2398_3 (m.d 0 1) (by simp) with h2427 | h2427
                      · rcases p2398_3 (m.d 0 2) (by simp) with h2428 | h2428
                        · rcases p2398_3 (m.d 0 3) (by simp) with h2429 | h2429
                          · linarith only [h2429, h4, hlam]
                          · rcases p2398_3 (m.d 0 4) (by simp) with h2431 | h2431
                            · linarith only [h2431, h5, hlam]
                            · rcases p2398_3 (m.d 0 5) (by simp) with h2433 | h2433
                              · linarith only [h2433, h6, hlam]
                              · linarith only [h1790, h2433, hlam]
                        · linarith only [h2428, h5, hlam]
                      · linarith only [h2, h2427, hlam]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      rcases p2398_3 (m.d 0 1) (by simp) with h2438 | h2438
                      · rcases p2398_3 (m.d 0 2) (by simp) with h2439 | h2439
                        · rcases p2398_3 (m.d 0 3) (by simp) with h2440 | h2440
                          · linarith only [h2440, h4, hlam]
                          · rcases p2398_3 (m.d 0 4) (by simp) with h2442 | h2442
                            · linarith only [h2442, h5, hlam]
                            · rcases p2398_3 (m.d 0 5) (by simp) with h2444 | h2444
                              · linarith only [h2444, h6, hlam]
                              · rcases h2bigk with h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2448 | h2448
                                  · rcases p2446_3 (m.d 1 2) (by simp) with h2449 | h2449
                                    · linarith only [h0, h2449, hlam]
                                    · rcases p2446_3 (m.d 2 3) (by simp) with h2451 | h2451
                                      · linarith only [h2451, h4, hlam]
                                      · rcases p2446_3 (m.d 2 4) (by simp) with h2453 | h2453
                                        · linarith only [h2453, h5, hlam]
                                        · rcases p2446_3 (m.d 2 5) (by simp) with h2455 | h2455
                                          · linarith only [h2455, h6, hlam]
                                          · rcases h3bigk with h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2071, h7, hc23, hc34, hlam, hphi, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2084, h7, hc23, hc45, hlam, hphi, ht34, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h7, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h1617, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h1, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h1, h2084, h7, hc23, hc45, hlam, hphi, ht34, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2074, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2076, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h4, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2071, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2078, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2080, hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2084, hc03, hc45, hlam, hphi, ht34, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2071, h2084, hc23, hc45, hlam, hphi, ht34, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2084, hc23, hc45, hlam, hphi, ht34, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [hlam, p2457_0]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h2084, hlam, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              rcases p2457_3 (m.d 0 3) (by simp) with h2478 | h2478
                                              · linarith only [h2478, hlam, p2457_0]
                                              · rcases p2457_3 (m.d 1 3) (by simp) with h2480 | h2480
                                                · linarith only [h2076, h2480, hlam]
                                                · rcases p2457_3 (m.d 2 3) (by simp) with h2482 | h2482
                                                  · linarith only [h2080, h2482, hlam]
                                                  · rcases p2457_3 (m.d 3 4) (by simp) with h2484 | h2484
                                                    · linarith only [h2084, h2484, hlam]
                                                    · linarith only [h2484, h7, hlam]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              rcases p2457_3 (m.d 0 3) (by simp) with h2487 | h2487
                                              · linarith only [h1617, h2487, hlam]
                                              · linarith only [h1, h2487, hlam]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              rcases p2457_3 (m.d 0 3) (by simp) with h2490 | h2490
                                              · linarith only [h1617, h2490, hlam]
                                              · linarith only [h2490, h4, hlam]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [h1, h2071, h2084, h7, hc23, hc45, hlam, hphi, ht34, p2457_1]
                                            · have p2457_0 := h2457c.1
                                              have p2457_1 := h2457c.2.1
                                              have p2457_2 := h2457c.2.2.1
                                              have p2457_3 := h2457c.2.2.2
                                              linarith only [hlam, p2457_0]
                                  · linarith only [h0, h2448, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2078, h2082, h6, hlam, p2398_1, p2446_2]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2082, h6, hlam, p2398_1, p2446_2]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h6, hlam, p2398_1, p2446_2]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2501 | h2501
                                  · rcases p2446_3 (m.d 1 2) (by simp) with h2502 | h2502
                                    · rcases p2446_3 (m.d 2 3) (by simp) with h2503 | h2503
                                      · linarith only [h2503, hlam, p2446_0]
                                      · rcases p2446_3 (m.d 2 4) (by simp) with h2505 | h2505
                                        · linarith only [h2072, h2505, hlam]
                                        · linarith only [h2078, h2505, hlam]
                                    · linarith only [h2502, hlam, p2446_0]
                                  · linarith only [h2501, h4, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2510 | h2510
                                  · rcases p2446_3 (m.d 1 2) (by simp) with h2511 | h2511
                                    · rcases p2446_3 (m.d 2 3) (by simp) with h2512 | h2512
                                      · linarith only [h2071, h2512, hlam]
                                      · rcases p2446_3 (m.d 2 4) (by simp) with h2514 | h2514
                                        · linarith only [h2514, hlam, p2446_0]
                                        · rcases p2446_3 (m.d 2 5) (by simp) with h2516 | h2516
                                          · linarith only [h2073, h2516, hlam]
                                          · linarith only [h2082, h2516, hlam]
                                    · linarith only [h2511, hlam, p2446_0]
                                  · linarith only [h2510, h5, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2521 | h2521
                                  · rcases p2446_3 (m.d 1 2) (by simp) with h2522 | h2522
                                    · rcases p2446_3 (m.d 2 3) (by simp) with h2523 | h2523
                                      · linarith only [h2071, h2523, hlam]
                                      · rcases p2446_3 (m.d 2 4) (by simp) with h2525 | h2525
                                        · linarith only [h2072, h2525, hlam]
                                        · rcases p2446_3 (m.d 2 5) (by simp) with h2527 | h2527
                                          · linarith only [h2527, hlam, p2446_0]
                                          · rcases h3bigk with h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h1790, h2071, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2398_1, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h0, h1790, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2398_1, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h7, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h1617, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h1, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h0, h1, h1790, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2398_1, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2074, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2076, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h4, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2071, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2078, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2080, hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2084, hc03, hc45, hlam, hphi, ht34, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2071, h2084, hc23, hc45, hlam, hphi, ht34, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2084, hc23, hc45, hlam, hphi, ht34, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [hlam, p2529_0]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h2084, hlam, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              rcases p2529_3 (m.d 0 3) (by simp) with h2550 | h2550
                                              · linarith only [h2550, hlam, p2529_0]
                                              · rcases p2529_3 (m.d 1 3) (by simp) with h2552 | h2552
                                                · linarith only [h2076, h2552, hlam]
                                                · rcases p2529_3 (m.d 2 3) (by simp) with h2554 | h2554
                                                  · linarith only [h2080, h2554, hlam]
                                                  · rcases p2529_3 (m.d 3 4) (by simp) with h2556 | h2556
                                                    · linarith only [h2084, h2556, hlam]
                                                    · linarith only [h2556, h7, hlam]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              rcases p2529_3 (m.d 0 3) (by simp) with h2559 | h2559
                                              · linarith only [h1617, h2559, hlam]
                                              · linarith only [h1, h2559, hlam]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              rcases p2529_3 (m.d 0 3) (by simp) with h2562 | h2562
                                              · linarith only [h1617, h2562, hlam]
                                              · linarith only [h2562, h4, hlam]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [h1, h2071, h2084, h7, hc23, hc45, hlam, hphi, ht34, p2529_1]
                                            · have p2529_0 := h2529c.1
                                              have p2529_1 := h2529c.2.1
                                              have p2529_2 := h2529c.2.2.1
                                              have p2529_3 := h2529c.2.2.2
                                              linarith only [hlam, p2529_0]
                                    · linarith only [h2522, hlam, p2446_0]
                                  · linarith only [h2521, h6, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h4, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2071, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2078, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2080, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h5, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2072, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h1790, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2398_1, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2082, hlam, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h6, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2073, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2398_1, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h2073, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2398_1, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                        · linarith only [h2439, h6, hlam]
                      · linarith only [h2438, h3, hlam]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h1, hlam, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h4, hlam, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h7, hlam, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h1617, hlam, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h2, hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h5, hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h1, h2071, h7, hc23, hc34, hlam, hphi, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h1790, hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h3, hlam, p2398_0]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h6, hlam, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h1, h1617, h2071, h2084, hc23, hc45, hlam, hphi, ht34, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [h1617, h2084, hc04, hc45, hlam, hphi, p2398_1]
                    · have p2398_0 := h2398c.1
                      have p2398_1 := h2398c.2.1
                      have p2398_2 := h2398c.2.2.1
                      have p2398_3 := h2398c.2.2.2
                      linarith only [hlam, p2398_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2601 | h2601
        · linarith only [h1, h2601, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2603 | h2603
          · linarith only [h1, h1617, h2073, h2603, h6, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2605 | h2605
            · linarith only [h2071, h2073, h2605, h6, h7, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2607 | h2607
              · linarith only [h1, h1617, h2071, h2607, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2609 | h2609
                · linarith only [h0, h1790, h2072, h2073, h2609, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2611 | h2611
                  · linarith only [h1790, h2072, h2073, h2605, h2611, h6, hc23, hc34, hlam, hphi]
                  · rcases h0bigk with h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h0, h2072, h2605, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      rcases p2613_3 (m.d 0 1) (by simp) with h2616 | h2616
                      · rcases p2613_3 (m.d 0 2) (by simp) with h2617 | h2617
                        · linarith only [h0, h2617, hlam]
                        · linarith only [h2617, h4, hlam]
                      · linarith only [h1, h2616, hlam]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      rcases p2613_3 (m.d 0 1) (by simp) with h2621 | h2621
                      · rcases p2613_3 (m.d 0 2) (by simp) with h2622 | h2622
                        · linarith only [h0, h2622, hlam]
                        · linarith only [h2622, h5, hlam]
                      · linarith only [h2, h2621, hlam]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h2072, h2073, h2605, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h0, hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      rcases p2613_3 (m.d 0 1) (by simp) with h2629 | h2629
                      · rcases p2613_3 (m.d 0 2) (by simp) with h2630 | h2630
                        · rcases p2613_3 (m.d 0 3) (by simp) with h2631 | h2631
                          · linarith only [h2631, h4, hlam]
                          · rcases p2613_3 (m.d 0 4) (by simp) with h2633 | h2633
                            · linarith only [h2633, h5, hlam]
                            · linarith only [h2633, h7, hlam]
                        · linarith only [h2630, h4, hlam]
                      · linarith only [h1, h2629, hlam]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      rcases p2613_3 (m.d 0 1) (by simp) with h2638 | h2638
                      · rcases p2613_3 (m.d 0 2) (by simp) with h2639 | h2639
                        · rcases p2613_3 (m.d 0 3) (by simp) with h2640 | h2640
                          · linarith only [h2640, h4, hlam]
                          · rcases p2613_3 (m.d 0 4) (by simp) with h2642 | h2642
                            · linarith only [h2642, h5, hlam]
                            · rcases p2613_3 (m.d 0 5) (by simp) with h2644 | h2644
                              · linarith only [h2644, h6, hlam]
                              · linarith only [h1790, h2644, hlam]
                        · linarith only [h2639, h5, hlam]
                      · linarith only [h2, h2638, hlam]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h0, h2072, h2073, h2605, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h1, hlam, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h4, hlam, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h7, hlam, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h1617, hlam, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h2, hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h5, hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h1, h2611, h7, hc13, hc45, hlam, hphi, ht34, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h1790, hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h3, hlam, p2613_0]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h6, hlam, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h1, h1617, hc13, hc35, hlam, hphi, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [h1790, hc04, hc45, hlam, hphi, p2613_1]
                    · have p2613_0 := h2613c.1
                      have p2613_1 := h2613c.2.1
                      have p2613_2 := h2613c.2.2.1
                      have p2613_3 := h2613c.2.2.2
                      linarith only [hlam, p2613_0]
    · linarith only [h1790, h2071, h2072, h5, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2666 | h2666
    · linarith only [h1790, h2071, h2666, h4, h7, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2668 | h2668
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2669 | h2669
        · linarith only [h2071, h2668, h2669, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2671 | h2671
          · linarith only [h1617, h2071, h2668, h2671, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2071, h2668, h2671, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2674 | h2674
        · linarith only [h1, h2674, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2676 | h2676
          · linarith only [h1617, h1790, h2071, h2668, h2676, h4, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2678 | h2678
            · linarith only [h2678, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2680 | h2680
              · linarith only [h1617, h2680, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2682 | h2682
                · linarith only [h1790, h2682, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2684 | h2684
                  · linarith only [h1790, h2071, h2684, h4, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h2071, h2684, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1617 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1790 | h1790
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1617 h1790
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1617 h1790

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h1617 | h1617
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1617
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1617

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2687 | h2687
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2688 | h2688
      · linarith only [h2688, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2690 | h2690
        · linarith only [h2687, h2690, h4, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2692 | h2692
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2693 | h2693
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2694 | h2694
              · linarith only [h0, h2694, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2696 | h2696
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2697 | h2697
                  · linarith only [h1, h2688, h2697, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2699 | h2699
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2700 | h2700
                      · linarith only [h0, h2688, h2692, h2700, h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2702 | h2702
                        · linarith only [h0, h2690, h2692, h2699, h2700, h2702, h6, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h2692, h2699, h2702, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h1, h2688, h2696, h2699, hc23, hc35, hlam, hphi]
                · linarith only [h2687, h2688, h2696, hc13, hc35, hlam, hphi]
            · linarith only [h2693, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h2692, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2709 | h2709
      · linarith only [h2709, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2711 | h2711
        · linarith only [h2711, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2713 | h2713
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2714 | h2714
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2715 | h2715
              · linarith only [h0, h2715, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2717 | h2717
                · linarith only [h1, h2687, h2717, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2719 | h2719
                  · linarith only [h1, h2709, h2719, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2721 | h2721
                    · linarith only [h0, h1, h2687, h2713, h2721, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2723 | h2723
                      · linarith only [h2709, h2723, h4, h6, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2725 | h2725
                        · linarith only [h0, h2711, h2714, h2725, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2727 | h2727
                          · linarith only [h0, h2714, h2721, h2725, h2727, h6, hc23, hc34, hlam, hphi]
                          · rcases h0bigk with h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c | h2729c
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h0, h2714, h2721, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              rcases p2729_3 (m.d 0 1) (by simp) with h2732 | h2732
                              · rcases p2729_3 (m.d 0 2) (by simp) with h2733 | h2733
                                · linarith only [h0, h2733, hlam]
                                · linarith only [h2733, h4, hlam]
                              · linarith only [h1, h2732, hlam]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              rcases p2729_3 (m.d 0 1) (by simp) with h2737 | h2737
                              · rcases p2729_3 (m.d 0 2) (by simp) with h2738 | h2738
                                · linarith only [h0, h2738, hlam]
                                · linarith only [h2738, h5, hlam]
                              · linarith only [h2, h2737, hlam]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h0, h2714, h2721, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h0, hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h1, h2713, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h1, h2687, h2713, h2723, h6, hc23, hc35, hlam, hphi, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h6, hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h1, hlam, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h4, hlam, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h2687, hlam, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h2709, hlam, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h2, hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h5, hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h1, h2713, h2723, h5, h6, hc23, hc35, hlam, hphi, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h2711, hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h3, hlam, p2729_0]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h0, h2714, h2721, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h1, h2713, h2723, h6, hc23, hc35, hlam, hphi, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [h2721, h2723, h5, h6, hc23, hc35, hlam, hphi, p2729_1]
                            · have p2729_0 := h2729c.1
                              have p2729_1 := h2729c.2.1
                              have p2729_2 := h2729c.2.2.1
                              have p2729_3 := h2729c.2.2.2
                              linarith only [hlam, p2729_0]
            · linarith only [h2714, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h2713, h4, h6, hc12, hc25, hlam, hphi]

end R2N4
