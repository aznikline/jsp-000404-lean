import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S2
import Jsp000404.R1LeavesN7_2S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h1352 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1513 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1627 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h2088 | h2088
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2089 | h2089
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2090 | h2090
      · linarith only [h0, h1627, h2088, h2090, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2092 | h2092
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2093 | h2093
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2094 | h2094
            · rcases h0bigk with h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h1513, h2090, h2092, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h1513, h2090, h2092, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h1513, h2090, h2092, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                rcases p2095_3 (m.d 0 1) (by simp) with h2100 | h2100
                · rcases p2095_3 (m.d 0 2) (by simp) with h2101 | h2101
                  · linarith only [h0, h2101, hlam]
                  · linarith only [h2101, h6, hlam]
                · linarith only [h2100, h3, hlam]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h0, hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h1513, h2090, h2092, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h0, h1513, h2090, h2092, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                rcases p2095_3 (m.d 0 1) (by simp) with h2109 | h2109
                · rcases p2095_3 (m.d 0 2) (by simp) with h2110 | h2110
                  · rcases p2095_3 (m.d 0 3) (by simp) with h2111 | h2111
                    · linarith only [h2111, h4, hlam]
                    · linarith only [h2111, h8, hlam]
                  · linarith only [h2110, h6, hlam]
                · linarith only [h2109, h3, hlam]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h1, hlam, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h4, hlam, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h1513, h2090, h2092, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                rcases p2095_3 (m.d 0 1) (by simp) with h2120 | h2120
                · rcases p2095_3 (m.d 0 2) (by simp) with h2121 | h2121
                  · rcases p2095_3 (m.d 0 3) (by simp) with h2122 | h2122
                    · rcases p2095_3 (m.d 0 4) (by simp) with h2123 | h2123
                      · linarith only [h2123, h7, hlam]
                      · linarith only [h2123, h9, hlam]
                    · linarith only [h2122, h8, hlam]
                  · linarith only [h2121, h6, hlam]
                · linarith only [h2120, h3, hlam]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h2, hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h5, hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h7, hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                rcases p2095_3 (m.d 0 1) (by simp) with h2133 | h2133
                · rcases p2095_3 (m.d 0 2) (by simp) with h2134 | h2134
                  · rcases p2095_3 (m.d 0 3) (by simp) with h2135 | h2135
                    · rcases p2095_3 (m.d 0 4) (by simp) with h2136 | h2136
                      · rcases p2095_3 (m.d 0 5) (by simp) with h2137 | h2137
                        · linarith only [h2137, h9, hlam]
                        · rcases h2bigk with h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c | h2139c
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h1513, h5, h6, hlam, p2095_1, p2139_2]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            rcases p2139_3 (m.d 0 2) (by simp) with h2142 | h2142
                            · rcases p2139_3 (m.d 1 2) (by simp) with h2143 | h2143
                              · linarith only [h0, h2143, hlam]
                              · rcases p2139_3 (m.d 2 3) (by simp) with h2145 | h2145
                                · linarith only [h2145, hlam, p2139_0]
                                · rcases p2139_3 (m.d 2 4) (by simp) with h2147 | h2147
                                  · linarith only [h2147, h5, hlam]
                                  · linarith only [h2090, h2147, hlam]
                            · linarith only [h2142, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            rcases p2139_3 (m.d 0 2) (by simp) with h2151 | h2151
                            · rcases p2139_3 (m.d 1 2) (by simp) with h2152 | h2152
                              · linarith only [h0, h2152, hlam]
                              · rcases p2139_3 (m.d 2 3) (by simp) with h2154 | h2154
                                · linarith only [h2154, h4, hlam]
                                · rcases p2139_3 (m.d 2 4) (by simp) with h2156 | h2156
                                  · linarith only [h2156, hlam, p2139_0]
                                  · rcases p2139_3 (m.d 2 5) (by simp) with h2158 | h2158
                                    · linarith only [h2158, h6, hlam]
                                    · rcases h3bigk with h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h2088, h2094, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h0, h1513, h2092, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h0, h1513, h2090, h2092, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        rcases p2160_3 (m.d 0 3) (by simp) with h2165 | h2165
                                        · rcases p2160_3 (m.d 1 3) (by simp) with h2166 | h2166
                                          · linarith only [h1, h2166, hlam]
                                          · linarith only [h2088, h2166, hlam]
                                        · linarith only [h2165, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h1, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h10, hlam, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h1627, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h1, h2094, hc01, hc45, hlam, hphi, ht0b, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h4, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h2090, hc13, hc34, hlam, hphi, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h2090, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h0, h2090, h2094, hc01, hc45, hlam, hphi, ht0b, ht5b, p2139_1, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h7, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h0, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h0, h2094, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2160_1]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h8, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h2088, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h2092, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [h2094, hlam, p2160_0]
                                      · have p2160_0 := h2160c.1
                                        have p2160_1 := h2160c.2.1
                                        have p2160_2 := h2160c.2.2.1
                                        have p2160_3 := h2160c.2.2.2
                                        linarith only [hlam, p2160_0]
                            · linarith only [h2151, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            rcases p2139_3 (m.d 0 2) (by simp) with h2191 | h2191
                            · rcases p2139_3 (m.d 1 2) (by simp) with h2192 | h2192
                              · linarith only [h0, h2192, hlam]
                              · rcases p2139_3 (m.d 2 3) (by simp) with h2194 | h2194
                                · linarith only [h2194, h4, hlam]
                                · linarith only [h2092, h2194, hlam]
                            · linarith only [h2191, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h0, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h10, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h1352, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h1513, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h4, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h0, h2090, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2139_1]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h2090, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h0, h1513, h2090, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2139_1]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h5, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            rcases p2139_3 (m.d 0 2) (by simp) with h2209 | h2209
                            · rcases p2139_3 (m.d 1 2) (by simp) with h2210 | h2210
                              · linarith only [h2210, hlam, p2139_0]
                              · rcases p2139_3 (m.d 2 3) (by simp) with h2212 | h2212
                                · linarith only [h2090, h2212, hlam]
                                · linarith only [h10, h2212, hlam]
                            · linarith only [h0, h2209, hlam]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h10, hc12, hc24, hlam, hphi, p2139_1]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h0, h1513, h2090, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2139_1]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h6, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2095_1, p2139_1]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h2092, hlam, p2139_1]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [h2093, hlam, p2139_0]
                          · have p2139_0 := h2139c.1
                            have p2139_1 := h2139c.2.1
                            have p2139_2 := h2139c.2.2.1
                            have p2139_3 := h2139c.2.2.2
                            linarith only [hlam, p2139_0]
                      · linarith only [h2136, h9, hlam]
                    · linarith only [h2135, h8, hlam]
                  · linarith only [h2134, h6, hlam]
                · linarith only [h2133, h3, hlam]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h3, hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h6, hlam, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h8, hlam, p2095_0]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [h9, hlam, p2095_1]
              · have p2095_0 := h2095c.1
                have p2095_1 := h2095c.2.1
                have p2095_2 := h2095c.2.2.1
                have p2095_3 := h2095c.2.2.2
                linarith only [hlam, p2095_0]
            · linarith only [h0, h10, h2090, h2094, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1352, h2089, h2093, hlam]
        · linarith only [h1, h10, h2088, h2092, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · linarith only [h1627, h2088, h2089, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2237 | h2237
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2238 | h2238
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2239 | h2239
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2240 | h2240
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2241 | h2241
            · rcases h0bigk with h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c | h2242c
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h1627, h2237, h2238, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h1627, h2237, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2246 | h2246
                · rcases p2242_3 (m.d 0 2) (by simp) with h2247 | h2247
                  · linarith only [h0, h2247, hlam]
                  · linarith only [h2247, h5, hlam]
                · linarith only [h2, h2246, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2251 | h2251
                · rcases p2242_3 (m.d 0 2) (by simp) with h2252 | h2252
                  · linarith only [h0, h2252, hlam]
                  · linarith only [h2252, h6, hlam]
                · linarith only [h2251, h3, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h0, hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h10, h2088, h2238, h2241, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2259 | h2259
                · rcases p2242_3 (m.d 0 2) (by simp) with h2260 | h2260
                  · rcases p2242_3 (m.d 0 3) (by simp) with h2261 | h2261
                    · linarith only [h2261, h4, hlam]
                    · linarith only [h2261, h7, hlam]
                  · linarith only [h2260, h5, hlam]
                · linarith only [h2, h2259, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2266 | h2266
                · rcases p2242_3 (m.d 0 2) (by simp) with h2267 | h2267
                  · rcases p2242_3 (m.d 0 3) (by simp) with h2268 | h2268
                    · linarith only [h2268, h4, hlam]
                    · linarith only [h2268, h8, hlam]
                  · linarith only [h2267, h6, hlam]
                · linarith only [h2266, h3, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h1, hlam, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h4, hlam, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2276 | h2276
                · rcases p2242_3 (m.d 0 2) (by simp) with h2277 | h2277
                  · rcases p2242_3 (m.d 0 3) (by simp) with h2278 | h2278
                    · rcases p2242_3 (m.d 0 4) (by simp) with h2279 | h2279
                      · linarith only [h2279, h7, hlam]
                      · rcases p2242_3 (m.d 0 5) (by simp) with h2281 | h2281
                        · linarith only [h2281, h8, hlam]
                        · rcases h2bigk with h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h10, h2088, h2238, h2241, h4, hlam, p2283_2]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h10, h2088, h2238, h2241, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            rcases p2283_3 (m.d 0 2) (by simp) with h2287 | h2287
                            · rcases p2283_3 (m.d 1 2) (by simp) with h2288 | h2288
                              · linarith only [h0, h2288, hlam]
                              · rcases p2283_3 (m.d 2 3) (by simp) with h2290 | h2290
                                · linarith only [h2290, h4, hlam]
                                · linarith only [h2238, h2290, hlam]
                            · linarith only [h2287, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            rcases p2283_3 (m.d 0 2) (by simp) with h2294 | h2294
                            · rcases p2283_3 (m.d 1 2) (by simp) with h2295 | h2295
                              · linarith only [h0, h2295, hlam]
                              · rcases p2283_3 (m.d 2 3) (by simp) with h2297 | h2297
                                · linarith only [h2297, h4, hlam]
                                · linarith only [h2239, h2297, hlam]
                            · linarith only [h2294, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h0, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h10, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h1352, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h1513, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h4, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            rcases p2283_3 (m.d 0 2) (by simp) with h2307 | h2307
                            · rcases p2283_3 (m.d 1 2) (by simp) with h2308 | h2308
                              · linarith only [h2308, hlam, p2283_0]
                              · rcases p2283_3 (m.d 2 3) (by simp) with h2310 | h2310
                                · rcases p2283_3 (m.d 2 4) (by simp) with h2311 | h2311
                                  · linarith only [h2238, h2311, hlam]
                                  · linarith only [h1352, h2311, hlam]
                                · linarith only [h2310, hlam, p2283_0]
                            · linarith only [h0, h2307, hlam]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h10, h2088, h2239, h2240, hc12, hc23, hlam, hphi, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h0, h10, h2088, h2239, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h5, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2242_1, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h2238, hlam, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h0, h10, h2088, h2239, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2242_1, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h6, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2242_1, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h2239, hlam, p2283_1]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [h2240, hlam, p2283_0]
                          · have p2283_0 := h2283c.1
                            have p2283_1 := h2283c.2.1
                            have p2283_2 := h2283c.2.2.1
                            have p2283_3 := h2283c.2.2.2
                            linarith only [hlam, p2283_0]
                    · linarith only [h2278, h7, hlam]
                  · linarith only [h2277, h5, hlam]
                · linarith only [h2, h2276, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2332 | h2332
                · rcases p2242_3 (m.d 0 2) (by simp) with h2333 | h2333
                  · rcases p2242_3 (m.d 0 3) (by simp) with h2334 | h2334
                    · rcases p2242_3 (m.d 0 4) (by simp) with h2335 | h2335
                      · linarith only [h2335, h7, hlam]
                      · linarith only [h2335, h9, hlam]
                    · linarith only [h2334, h8, hlam]
                  · linarith only [h2333, h6, hlam]
                · linarith only [h2332, h3, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h2, hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h5, hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h7, hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                rcases p2242_3 (m.d 0 1) (by simp) with h2345 | h2345
                · rcases p2242_3 (m.d 0 2) (by simp) with h2346 | h2346
                  · rcases p2242_3 (m.d 0 3) (by simp) with h2347 | h2347
                    · rcases p2242_3 (m.d 0 4) (by simp) with h2348 | h2348
                      · rcases p2242_3 (m.d 0 5) (by simp) with h2349 | h2349
                        · linarith only [h2349, h9, hlam]
                        · rcases h2bigk with h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c | h2351c
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h10, h2088, h4, h7, h8, hlam, p2242_1, p2351_2]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h0, h10, h2088, h2238, h2241, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            rcases p2351_3 (m.d 0 2) (by simp) with h2355 | h2355
                            · rcases p2351_3 (m.d 1 2) (by simp) with h2356 | h2356
                              · linarith only [h0, h2356, hlam]
                              · rcases p2351_3 (m.d 2 3) (by simp) with h2358 | h2358
                                · linarith only [h2358, h4, hlam]
                                · linarith only [h2238, h2358, hlam]
                            · linarith only [h2355, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            rcases p2351_3 (m.d 0 2) (by simp) with h2362 | h2362
                            · rcases p2351_3 (m.d 1 2) (by simp) with h2363 | h2363
                              · linarith only [h0, h2363, hlam]
                              · rcases p2351_3 (m.d 2 3) (by simp) with h2365 | h2365
                                · linarith only [h2365, h4, hlam]
                                · linarith only [h2239, h2365, hlam]
                            · linarith only [h2362, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h0, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h10, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h1352, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h1513, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h4, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            rcases p2351_3 (m.d 0 2) (by simp) with h2375 | h2375
                            · rcases p2351_3 (m.d 1 2) (by simp) with h2376 | h2376
                              · linarith only [h2376, hlam, p2351_0]
                              · rcases p2351_3 (m.d 2 3) (by simp) with h2378 | h2378
                                · rcases p2351_3 (m.d 2 4) (by simp) with h2379 | h2379
                                  · linarith only [h2238, h2379, hlam]
                                  · linarith only [h1352, h2379, hlam]
                                · linarith only [h2378, hlam, p2351_0]
                            · linarith only [h0, h2375, hlam]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h1352, hc12, hc23, hlam, hphi, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h0, h1513, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h5, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            rcases p2351_3 (m.d 0 2) (by simp) with h2388 | h2388
                            · rcases p2351_3 (m.d 1 2) (by simp) with h2389 | h2389
                              · linarith only [h2389, hlam, p2351_0]
                              · rcases p2351_3 (m.d 2 3) (by simp) with h2391 | h2391
                                · rcases p2351_3 (m.d 2 4) (by simp) with h2392 | h2392
                                  · rcases p2351_3 (m.d 2 5) (by simp) with h2393 | h2393
                                    · linarith only [h2240, h2393, hlam]
                                    · linarith only [h1513, h2393, hlam]
                                  · linarith only [h2392, hlam, p2351_0]
                                · linarith only [h10, h2391, hlam]
                            · linarith only [h0, h2388, hlam]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h2238, hlam, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h10, h2088, h2239, hc12, hc24, hlam, hphi, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h6, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2242_1, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h2239, hlam, p2351_1]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [h2240, hlam, p2351_0]
                          · have p2351_0 := h2351c.1
                            have p2351_1 := h2351c.2.1
                            have p2351_2 := h2351c.2.2.1
                            have p2351_3 := h2351c.2.2.2
                            linarith only [hlam, p2351_0]
                      · linarith only [h2348, h9, hlam]
                    · linarith only [h2347, h8, hlam]
                  · linarith only [h2346, h6, hlam]
                · linarith only [h2345, h3, hlam]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h3, hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h6, hlam, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h8, hlam, p2242_0]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [h9, hlam, p2242_1]
              · have p2242_0 := h2242c.1
                have p2242_1 := h2242c.2.1
                have p2242_2 := h2242c.2.2.1
                have p2242_3 := h2242c.2.2.2
                linarith only [hlam, p2242_0]
            · linarith only [h10, h1627, h2, h2237, h2241, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h0, h1627, h2237, h2238, h2240, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1627, h2237, h2238, h2239, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2419 | h2419
        · linarith only [h10, h2088, h2238, h2419, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2421 | h2421
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2422 | h2422
            · rcases h0bigk with h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h10, h2419, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h10, h2419, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h10, h2419, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h0, hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h0, h10, h2419, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h0, h10, h2419, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h0, h10, h2419, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h1, hlam, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h4, hlam, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h0, h10, h2419, h4, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h0, h10, h2419, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h2, hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h5, hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h7, hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h10, h2419, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h3, hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h6, hlam, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h8, hlam, p2423_0]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [h9, hlam, p2423_1]
              · have p2423_0 := h2423c.1
                have p2423_1 := h2423c.2.1
                have p2423_2 := h2423c.2.2.1
                have p2423_3 := h2423c.2.2.2
                linarith only [hlam, p2423_0]
            · linarith only [h1352, h2237, h2238, h2422, hlam]
          · linarith only [h1352, h2237, h2421, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2451 | h2451
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2452 | h2452
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2453 | h2453
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2454 | h2454
            · linarith only [h0, h10, h1627, h2237, h2451, h2454, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h10, h1627, h2453, h2454, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2457 | h2457
            · linarith only [h2451, h2453, h2457, hlam]
            · rcases h0bigk with h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h2088, h2452, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h10, h1627, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h10, h1627, h2451, h2453, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h10, h1627, h2451, h2453, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h0, hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h10, h1627, h2451, h2453, h7, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h0, h10, h1627, h2451, h2453, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h0, h10, h1627, h2451, h2453, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h1, hlam, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h4, hlam, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h10, h1627, h2451, h2453, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h0, h10, h1627, h2451, h2453, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h2, hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h5, hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h7, hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h0, h10, h1627, h2451, h2453, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h3, hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h6, hlam, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h8, hlam, p2459_0]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [h9, hlam, p2459_1]
              · have p2459_0 := h2459c.1
                have p2459_1 := h2459c.2.1
                have p2459_2 := h2459c.2.2.1
                have p2459_3 := h2459c.2.2.2
                linarith only [hlam, p2459_0]
        · linarith only [h10, h1627, h2451, h2452, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2486 | h2486
        · linarith only [h0, h10, h2088, h2451, h2486, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2488 | h2488
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2489 | h2489
            · rcases h0bigk with h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c | h2490c
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h2486, h2489, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h2486, h2489, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h10, h1627, h2237, h2488, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h10, h2486, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h0, hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h10, h2486, h2489, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h0, h10, h1627, h2237, h2488, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h0, h10, h2486, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h1, hlam, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h4, hlam, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h10, h1627, h2237, h2488, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h0, h10, h2486, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h2, hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h5, hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h7, hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h10, h2486, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h3, hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h6, hlam, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h8, hlam, p2490_0]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [h9, hlam, p2490_1]
              · have p2490_0 := h2490c.1
                have p2490_1 := h2490c.2.1
                have p2490_2 := h2490c.2.2.1
                have p2490_3 := h2490c.2.2.2
                linarith only [hlam, p2490_0]
            · linarith only [h2451, h2488, h2489, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2517 | h2517
            · linarith only [h0, h1352, h2488, h2517, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h10, h2451, h2517, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h1352 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1513 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h1627 | h1627
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1352 h1513 h1627
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1352 h1513 h1627

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h1352 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h1513 | h1513
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1352 h1513
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1352 h1513

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h1352 | h1352
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1352
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h1352

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10

set_option maxHeartbeats 8110000 in
set_option maxHeartbeats 8110000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s8_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  exact r1l7_10_12_23_L_I_L_I_H_I_s9 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

end R2N4
