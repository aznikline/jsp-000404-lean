import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1842 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2003 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2071 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2072 | h2072
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2073 | h2073
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2074 | h2074
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2075 | h2075
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2076 | h2076
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2077 | h2077
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2078 | h2078
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2079 | h2079
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2080 | h2080
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2081 | h2081
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2082 | h2082
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2083 | h2083
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2084 | h2084
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2085 | h2085
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2086 | h2086
                              · linarith only [h2071, h2083, h2086, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h2071, h2083, h2085, h2086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2089 | h2089
                              · linarith only [h2083, h2085, h2089, hlam]
                              · rcases h1bigk with h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h0, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h1652, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h1842, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2003, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  rcases p2091_3 (m.d 0 1) (by simp) with h2097 | h2097
                                  · linarith only [h2097, hlam, p2091_0]
                                  · rcases p2091_3 (m.d 1 2) (by simp) with h2099 | h2099
                                    · rcases p2091_3 (m.d 1 3) (by simp) with h2100 | h2100
                                      · linarith only [h2077, h2100, hlam]
                                      · linarith only [h1652, h2100, hlam]
                                    · linarith only [h2099, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h1652, hc01, hc12, hlam, hphi, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h1842, hc01, hc12, hlam, hphi, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2003, hc01, hc12, hlam, hphi, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  rcases p2091_3 (m.d 0 1) (by simp) with h2108 | h2108
                                  · linarith only [h2108, hlam, p2091_0]
                                  · rcases p2091_3 (m.d 1 2) (by simp) with h2110 | h2110
                                    · rcases p2091_3 (m.d 1 3) (by simp) with h2111 | h2111
                                      · rcases p2091_3 (m.d 1 4) (by simp) with h2112 | h2112
                                        · linarith only [h2080, h2112, hlam]
                                        · linarith only [h1842, h2112, hlam]
                                      · linarith only [h2111, hlam, p2091_0]
                                    · linarith only [h0, h2110, hlam]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2077, hlam, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h1842, h2076, h2083, h2085, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2091_1, u3ehi3]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2003, h2077, hc01, hc12, hlam, hphi, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  rcases p2091_3 (m.d 0 1) (by simp) with h2121 | h2121
                                  · linarith only [h2121, hlam, p2091_0]
                                  · rcases p2091_3 (m.d 1 2) (by simp) with h2123 | h2123
                                    · rcases p2091_3 (m.d 1 3) (by simp) with h2124 | h2124
                                      · rcases p2091_3 (m.d 1 4) (by simp) with h2125 | h2125
                                        · rcases p2091_3 (m.d 1 5) (by simp) with h2126 | h2126
                                          · linarith only [h2082, h2126, hlam]
                                          · linarith only [h2003, h2126, hlam]
                                        · linarith only [h2125, hlam, p2091_0]
                                      · linarith only [h1652, h2124, hlam]
                                    · linarith only [h0, h2123, hlam]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2078, hlam, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2080, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2003, h2076, h2083, h2085, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2091_1, u3ehi3]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  rcases p2091_3 (m.d 0 1) (by simp) with h2136 | h2136
                                  · linarith only [h2136, hlam, p2091_0]
                                  · rcases p2091_3 (m.d 1 2) (by simp) with h2138 | h2138
                                    · rcases p2091_3 (m.d 1 3) (by simp) with h2139 | h2139
                                      · rcases p2091_3 (m.d 1 4) (by simp) with h2140 | h2140
                                        · rcases p2091_3 (m.d 1 5) (by simp) with h2141 | h2141
                                          · rcases h5bigk with h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2003, hlam, p2142_1]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              rcases p2142_3 (m.d 0 5) (by simp) with h2145 | h2145
                                              · rcases p2142_3 (m.d 1 5) (by simp) with h2146 | h2146
                                                · rcases p2142_3 (m.d 2 5) (by simp) with h2147 | h2147
                                                  · linarith only [h2073, h2147, hlam]
                                                  · rcases p2142_3 (m.d 3 5) (by simp) with h2149 | h2149
                                                    · linarith only [h2075, h2149, hlam]
                                                    · rcases p2142_3 (m.d 4 5) (by simp) with h2151 | h2151
                                                      · linarith only [h2076, h2151, hlam]
                                                      · linarith only [h2085, h2151, hlam]
                                                · linarith only [h2079, h2146, hlam]
                                              · linarith only [h2073, h2145, hlam]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              rcases p2142_3 (m.d 0 5) (by simp) with h2156 | h2156
                                              · rcases p2142_3 (m.d 1 5) (by simp) with h2157 | h2157
                                                · rcases p2142_3 (m.d 2 5) (by simp) with h2158 | h2158
                                                  · linarith only [h2073, h2158, hlam]
                                                  · linarith only [h2084, h2158, hlam]
                                                · linarith only [h2081, h2157, hlam]
                                              · linarith only [h2075, h2156, hlam]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h1842, h2076, h2077, h2080, h2083, h2085, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2076, h2077, h2080, h2082, h2083, h2085, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              rcases p2142_3 (m.d 0 5) (by simp) with h2166 | h2166
                                              · linarith only [h2003, h2166, hlam]
                                              · linarith only [h2073, h2166, hlam]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              rcases p2142_3 (m.d 0 5) (by simp) with h2169 | h2169
                                              · linarith only [h2003, h2169, hlam]
                                              · linarith only [h2075, h2169, hlam]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2077, h2080, h2082, h2083, h2085, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2073, hlam, p2142_1]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2079, hlam, p2142_1]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h0, h2073, h2089, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2085, hlam, p2142_1]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2075, hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2081, hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2084, hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2089, hlam, p2142_1]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2076, hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h2082, hlam, p2142_0]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h1842, h2076, h2077, h2080, hc12, hlam, hphi, ht01, ht0b, ht5b, p2142_1, u5ehi2]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [h1842, h2076, h2077, h2080, h2089, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                            · have p2142_0 := h2142c.1
                                              have p2142_1 := h2142c.2.1
                                              have p2142_2 := h2142c.2.2.1
                                              have p2142_3 := h2142c.2.2.2
                                              linarith only [hlam, p2142_0]
                                          · linarith only [h2141, hlam, p2091_0]
                                        · linarith only [h1842, h2140, hlam]
                                      · linarith only [h1652, h2139, hlam]
                                    · linarith only [h0, h2138, hlam]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2079, hlam, p2091_1]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2081, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [h2082, hlam, p2091_0]
                                · have p2091_0 := h2091c.1
                                  have p2091_1 := h2091c.2.1
                                  have p2091_2 := h2091c.2.2.1
                                  have p2091_3 := h2091c.2.2.2
                                  linarith only [hlam, p2091_0]
                          · linarith only [h1652, h2075, h2077, h2083, h2084, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2197 | h2197
                          · linarith only [h2083, h2197, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2199 | h2199
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2200 | h2200
                              · rcases h1bigk with h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h0, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h1652, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h1842, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2003, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  rcases p2201_3 (m.d 0 1) (by simp) with h2207 | h2207
                                  · linarith only [h2207, hlam, p2201_0]
                                  · rcases p2201_3 (m.d 1 2) (by simp) with h2209 | h2209
                                    · rcases p2201_3 (m.d 1 3) (by simp) with h2210 | h2210
                                      · linarith only [h2077, h2210, hlam]
                                      · linarith only [h1652, h2210, hlam]
                                    · linarith only [h2209, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h1652, h2074, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2201_1, u3ehi3]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2003, h2075, h2082, h2197, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2201_1, u3ehi2]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2003, h2075, h2197, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2201_1, u3ehi2]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  rcases p2201_3 (m.d 0 1) (by simp) with h2218 | h2218
                                  · linarith only [h2218, hlam, p2201_0]
                                  · rcases p2201_3 (m.d 1 2) (by simp) with h2220 | h2220
                                    · rcases p2201_3 (m.d 1 3) (by simp) with h2221 | h2221
                                      · rcases p2201_3 (m.d 1 4) (by simp) with h2222 | h2222
                                        · linarith only [h2080, h2222, hlam]
                                        · linarith only [h1842, h2222, hlam]
                                      · linarith only [h2221, hlam, p2201_0]
                                    · linarith only [h0, h2220, hlam]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2077, hlam, p2201_1]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2003, h2075, h2082, h2197, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2201_1, u3ehi2]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2003, h2075, h2077, h2197, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2201_1, u3ehi2]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  rcases p2201_3 (m.d 0 1) (by simp) with h2231 | h2231
                                  · linarith only [h2231, hlam, p2201_0]
                                  · rcases p2201_3 (m.d 1 2) (by simp) with h2233 | h2233
                                    · rcases p2201_3 (m.d 1 3) (by simp) with h2234 | h2234
                                      · rcases p2201_3 (m.d 1 4) (by simp) with h2235 | h2235
                                        · rcases p2201_3 (m.d 1 5) (by simp) with h2236 | h2236
                                          · linarith only [h2082, h2236, hlam]
                                          · linarith only [h2003, h2236, hlam]
                                        · linarith only [h2235, hlam, p2201_0]
                                      · linarith only [h1652, h2234, hlam]
                                    · linarith only [h0, h2233, hlam]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2078, hlam, p2201_1]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2080, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2003, h2075, h2197, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2201_1, u3ehi2]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  rcases p2201_3 (m.d 0 1) (by simp) with h2246 | h2246
                                  · linarith only [h2246, hlam, p2201_0]
                                  · rcases p2201_3 (m.d 1 2) (by simp) with h2248 | h2248
                                    · rcases p2201_3 (m.d 1 3) (by simp) with h2249 | h2249
                                      · rcases p2201_3 (m.d 1 4) (by simp) with h2250 | h2250
                                        · rcases p2201_3 (m.d 1 5) (by simp) with h2251 | h2251
                                          · rcases h5bigk with h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c | h2252c
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2003, hlam, p2252_1]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              rcases p2252_3 (m.d 0 5) (by simp) with h2255 | h2255
                                              · rcases p2252_3 (m.d 1 5) (by simp) with h2256 | h2256
                                                · rcases p2252_3 (m.d 2 5) (by simp) with h2257 | h2257
                                                  · linarith only [h2073, h2257, hlam]
                                                  · rcases p2252_3 (m.d 3 5) (by simp) with h2259 | h2259
                                                    · linarith only [h2075, h2259, hlam]
                                                    · linarith only [h2197, h2259, hlam]
                                                · linarith only [h2079, h2256, hlam]
                                              · linarith only [h2073, h2255, hlam]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2074, h2076, h2197, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2252_1, u3ehi2]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              rcases p2252_3 (m.d 0 5) (by simp) with h2265 | h2265
                                              · rcases p2252_3 (m.d 1 5) (by simp) with h2266 | h2266
                                                · rcases p2252_3 (m.d 2 5) (by simp) with h2267 | h2267
                                                  · linarith only [h2073, h2267, hlam]
                                                  · linarith only [h2199, h2267, hlam]
                                                · linarith only [h2082, h2266, hlam]
                                              · linarith only [h2076, h2265, hlam]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2075, h2197, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2252_1, u3ehi2]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              rcases p2252_3 (m.d 0 5) (by simp) with h2274 | h2274
                                              · linarith only [h2003, h2274, hlam]
                                              · linarith only [h2073, h2274, hlam]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2077, h2080, h2082, h2197, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2252_1, u3ehi2]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              rcases p2252_3 (m.d 0 5) (by simp) with h2278 | h2278
                                              · linarith only [h2003, h2278, hlam]
                                              · linarith only [h2076, h2278, hlam]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2073, hlam, p2252_1]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2079, hlam, p2252_1]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2197, hlam, p2252_1]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h0, h2073, hc12, hlam, hphi, ht01, ht0b, ht5b, p2252_1, u5ehi4]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2075, hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2081, hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h1652, h2074, h2077, h2200, hc12, hlam, hphi, ht01, ht0b, ht5b, p2252_1, u5ehi2]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h1652, h2074, h2077, h2200, hc12, hlam, hphi, ht01, ht0b, ht5b, p2252_1, u5ehi4]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2076, hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2082, hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2199, hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [h2200, hlam, p2252_0]
                                            · have p2252_0 := h2252c.1
                                              have p2252_1 := h2252c.2.1
                                              have p2252_2 := h2252c.2.2.1
                                              have p2252_3 := h2252c.2.2.2
                                              linarith only [hlam, p2252_0]
                                          · linarith only [h2251, hlam, p2201_0]
                                        · linarith only [h1842, h2250, hlam]
                                      · linarith only [h1652, h2249, hlam]
                                    · linarith only [h0, h2248, hlam]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2079, hlam, p2201_1]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2081, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [h2082, hlam, p2201_0]
                                · have p2201_0 := h2201c.1
                                  have p2201_1 := h2201c.2.1
                                  have p2201_2 := h2201c.2.2.1
                                  have p2201_3 := h2201c.2.2.2
                                  linarith only [hlam, p2201_0]
                              · linarith only [h0, h2072, h2199, h2200, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2305 | h2305
                              · linarith only [h1652, h2074, h2077, h2083, h2199, h2305, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h1652, h2074, h2076, h2077, h2083, h2305, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1652, h1842, h2074, h2076, h2077, h2082, hc01, hc12, hlam, hphi]
                    · linarith only [h1652, h2074, h2081, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1652, h2074, h2080, hlam]
                · linarith only [h0, h2073, h2079, hlam]
              · linarith only [h0, h2072, h2078, hlam]
            · linarith only [h0, h2071, h2077, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2314 | h2314
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2315 | h2315
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2316 | h2316
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2317 | h2317
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2318 | h2318
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2319 | h2319
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2320 | h2320
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2321 | h2321
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2322 | h2322
                            · linarith only [h2072, h2076, h2322, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2324 | h2324
                              · linarith only [h2071, h2076, h2320, h2324, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h1bigk with h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h0, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h1652, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h1842, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2003, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  rcases p2326_3 (m.d 0 1) (by simp) with h2332 | h2332
                                  · linarith only [h2332, hlam, p2326_0]
                                  · rcases p2326_3 (m.d 1 2) (by simp) with h2334 | h2334
                                    · rcases p2326_3 (m.d 1 3) (by simp) with h2335 | h2335
                                      · linarith only [h2314, h2335, hlam]
                                      · linarith only [h1652, h2335, hlam]
                                    · linarith only [h2334, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2072, h2076, h2317, h2319, h2320, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2326_1, u3ehi3]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2072, h2076, h2319, h2320, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2326_1, u3ehi3]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2003, hc01, hc12, hlam, hphi, p2326_1]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  rcases p2326_3 (m.d 0 1) (by simp) with h2343 | h2343
                                  · linarith only [h2343, hlam, p2326_0]
                                  · rcases p2326_3 (m.d 1 2) (by simp) with h2345 | h2345
                                    · rcases p2326_3 (m.d 1 3) (by simp) with h2346 | h2346
                                      · rcases p2326_3 (m.d 1 4) (by simp) with h2347 | h2347
                                        · linarith only [h2317, h2347, hlam]
                                        · linarith only [h1842, h2347, hlam]
                                      · linarith only [h2346, hlam, p2326_0]
                                    · linarith only [h0, h2345, hlam]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2314, hlam, p2326_1]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2072, h2076, h2319, h2320, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2326_1, u3ehi3]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2072, h2076, h2314, h2319, h2320, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2326_1, u3ehi3]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  rcases p2326_3 (m.d 0 1) (by simp) with h2356 | h2356
                                  · linarith only [h2356, hlam, p2326_0]
                                  · rcases p2326_3 (m.d 1 2) (by simp) with h2358 | h2358
                                    · rcases p2326_3 (m.d 1 3) (by simp) with h2359 | h2359
                                      · rcases p2326_3 (m.d 1 4) (by simp) with h2360 | h2360
                                        · rcases p2326_3 (m.d 1 5) (by simp) with h2361 | h2361
                                          · linarith only [h2319, h2361, hlam]
                                          · linarith only [h2003, h2361, hlam]
                                        · linarith only [h2360, hlam, p2326_0]
                                      · linarith only [h1652, h2359, hlam]
                                    · linarith only [h0, h2358, hlam]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2315, hlam, p2326_1]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2317, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2072, h2076, h2319, h2320, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2326_1, u3ehi3]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  rcases p2326_3 (m.d 0 1) (by simp) with h2371 | h2371
                                  · linarith only [h2371, hlam, p2326_0]
                                  · rcases p2326_3 (m.d 1 2) (by simp) with h2373 | h2373
                                    · rcases p2326_3 (m.d 1 3) (by simp) with h2374 | h2374
                                      · rcases p2326_3 (m.d 1 4) (by simp) with h2375 | h2375
                                        · rcases p2326_3 (m.d 1 5) (by simp) with h2376 | h2376
                                          · rcases h5bigk with h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c | h2377c
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2003, hlam, p2377_1]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2076, h2321, hc45, hlam, hphi, ht34, p2377_1, u3ehi4]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2076, hc45, hlam, hphi, ht34, p2377_1, u3ehi4]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2076, hlam, p2377_1]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              rcases p2377_3 (m.d 0 5) (by simp) with h2383 | h2383
                                              · linarith only [h2003, h2383, hlam]
                                              · rcases p2377_3 (m.d 1 5) (by simp) with h2385 | h2385
                                                · rcases p2377_3 (m.d 2 5) (by simp) with h2386 | h2386
                                                  · linarith only [h2316, h2386, hlam]
                                                  · rcases p2377_3 (m.d 3 5) (by simp) with h2388 | h2388
                                                    · linarith only [h2318, h2388, hlam]
                                                    · rcases p2377_3 (m.d 4 5) (by simp) with h2390 | h2390
                                                      · linarith only [h2319, h2390, hlam]
                                                      · linarith only [h2076, h2390, hlam]
                                                · linarith only [h2003, h2385, hlam]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              rcases p2377_3 (m.d 0 5) (by simp) with h2395 | h2395
                                              · linarith only [h2003, h2395, hlam]
                                              · linarith only [h2073, h2395, hlam]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              rcases p2377_3 (m.d 0 5) (by simp) with h2398 | h2398
                                              · linarith only [h2003, h2398, hlam]
                                              · linarith only [h2075, h2398, hlam]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2072, h2076, h2314, h2317, h2319, h2320, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2377_1, u3ehi3]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2073, hlam, p2377_1]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2316, hlam, p2377_1]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h0, h2073, h2324, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2377_1, u3ehi3]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2322, hlam, p2377_1]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2075, hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2318, hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2321, hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2324, hlam, p2377_1]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2075, h2324, hc45, hlam, hphi, ht34, p2377_1, u3ehi3]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2319, hlam, p2377_0]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2314, h2317, h2319, h2321, h2324, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2377_1, u3ehi3]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [h2314, h2317, h2319, h2324, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2377_1, u3ehi3]
                                            · have p2377_0 := h2377c.1
                                              have p2377_1 := h2377c.2.1
                                              have p2377_2 := h2377c.2.2.1
                                              have p2377_3 := h2377c.2.2.2
                                              linarith only [hlam, p2377_0]
                                          · linarith only [h2376, hlam, p2326_0]
                                        · linarith only [h1842, h2375, hlam]
                                      · linarith only [h1652, h2374, hlam]
                                    · linarith only [h0, h2373, hlam]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2316, hlam, p2326_1]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2318, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [h2319, hlam, p2326_0]
                                · have p2326_0 := h2326c.1
                                  have p2326_1 := h2326c.2.1
                                  have p2326_2 := h2326c.2.2.1
                                  have p2326_3 := h2326c.2.2.2
                                  linarith only [hlam, p2326_0]
                          · linarith only [h2075, h2076, h2314, h2317, h2319, h2320, h2321, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h2074, h2076, h2314, h2317, h2319, h2320, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2427 | h2427
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2428 | h2428
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2429 | h2429
                            · linarith only [h1842, h2072, h2319, h2429, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2431 | h2431
                              · linarith only [h1842, h2072, h2319, h2427, h2431, hlam]
                              · rcases h1bigk with h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h0, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h1652, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h1842, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2003, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  rcases p2433_3 (m.d 0 1) (by simp) with h2439 | h2439
                                  · linarith only [h2439, hlam, p2433_0]
                                  · rcases p2433_3 (m.d 1 2) (by simp) with h2441 | h2441
                                    · rcases p2433_3 (m.d 1 3) (by simp) with h2442 | h2442
                                      · linarith only [h2314, h2442, hlam]
                                      · linarith only [h1652, h2442, hlam]
                                    · linarith only [h2441, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h1652, hc01, hc12, hlam, hphi, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h1842, hc01, hc12, hlam, hphi, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2003, hc01, hc12, hlam, hphi, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  rcases p2433_3 (m.d 0 1) (by simp) with h2450 | h2450
                                  · linarith only [h2450, hlam, p2433_0]
                                  · rcases p2433_3 (m.d 1 2) (by simp) with h2452 | h2452
                                    · rcases p2433_3 (m.d 1 3) (by simp) with h2453 | h2453
                                      · rcases p2433_3 (m.d 1 4) (by simp) with h2454 | h2454
                                        · linarith only [h2317, h2454, hlam]
                                        · linarith only [h1842, h2454, hlam]
                                      · linarith only [h2453, hlam, p2433_0]
                                    · linarith only [h0, h2452, hlam]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2314, hlam, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h1842, hc01, hc13, hlam, hphi, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2003, h2314, hc01, hc12, hlam, hphi, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2319, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2315, hlam, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2317, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2319, hlam, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  rcases p2433_3 (m.d 0 1) (by simp) with h2468 | h2468
                                  · linarith only [h2468, hlam, p2433_0]
                                  · rcases p2433_3 (m.d 1 2) (by simp) with h2470 | h2470
                                    · rcases p2433_3 (m.d 1 3) (by simp) with h2471 | h2471
                                      · rcases p2433_3 (m.d 1 4) (by simp) with h2472 | h2472
                                        · linarith only [h2319, h2472, hlam]
                                        · linarith only [h1842, h2472, hlam]
                                      · linarith only [h1652, h2471, hlam]
                                    · linarith only [h0, h2470, hlam]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2316, hlam, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h2318, hlam, p2433_0]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [h1842, hc01, hc15, hlam, hphi, p2433_1]
                                · have p2433_0 := h2433c.1
                                  have p2433_1 := h2433c.2.1
                                  have p2433_2 := h2433c.2.2.1
                                  have p2433_3 := h2433c.2.2.2
                                  linarith only [hlam, p2433_0]
                          · linarith only [h1652, h2075, h2314, h2427, h2428, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h2074, h2076, h2427, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h1652, h2075, h2318, hlam]
                  · linarith only [h1652, h2074, h2076, h2317, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h0, h2073, h2316, hlam]
              · linarith only [h0, h2072, h2076, h2315, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h2071, h2314, hlam]
        · linarith only [h2074, h2075, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2489 | h2489
        · linarith only [h2074, h2489, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2491 | h2491
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2492 | h2492
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2493 | h2493
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2494 | h2494
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2495 | h2495
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2496 | h2496
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2497 | h2497
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2498 | h2498
                        · linarith only [h2071, h2074, h2498, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2500 | h2500
                          · linarith only [h2071, h2489, h2500, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2502 | h2502
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2503 | h2503
                              · rcases h1bigk with h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c | h2504c
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h0, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h1652, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h1842, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2003, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  rcases p2504_3 (m.d 0 1) (by simp) with h2510 | h2510
                                  · linarith only [h2510, hlam, p2504_0]
                                  · rcases p2504_3 (m.d 1 2) (by simp) with h2512 | h2512
                                    · rcases p2504_3 (m.d 1 3) (by simp) with h2513 | h2513
                                      · linarith only [h2492, h2513, hlam]
                                      · linarith only [h1652, h2513, hlam]
                                    · linarith only [h2512, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2489, h2495, h2503, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2504_1, u3ehi0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2071, h2489, h2496, h2497, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2504_1, u3ehi2]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2071, h2489, h2496, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2504_1, u3ehi2]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  rcases p2504_3 (m.d 0 1) (by simp) with h2521 | h2521
                                  · linarith only [h2521, hlam, p2504_0]
                                  · rcases p2504_3 (m.d 1 2) (by simp) with h2523 | h2523
                                    · rcases p2504_3 (m.d 1 3) (by simp) with h2524 | h2524
                                      · rcases p2504_3 (m.d 1 4) (by simp) with h2525 | h2525
                                        · linarith only [h2495, h2525, hlam]
                                        · linarith only [h1842, h2525, hlam]
                                      · linarith only [h2524, hlam, p2504_0]
                                    · linarith only [h0, h2523, hlam]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2492, hlam, p2504_1]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2071, h2489, h2496, h2497, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2504_1, u3ehi2]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2071, h2489, h2492, h2496, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2504_1, u3ehi2]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  rcases p2504_3 (m.d 0 1) (by simp) with h2534 | h2534
                                  · linarith only [h2534, hlam, p2504_0]
                                  · rcases p2504_3 (m.d 1 2) (by simp) with h2536 | h2536
                                    · rcases p2504_3 (m.d 1 3) (by simp) with h2537 | h2537
                                      · rcases p2504_3 (m.d 1 4) (by simp) with h2538 | h2538
                                        · rcases p2504_3 (m.d 1 5) (by simp) with h2539 | h2539
                                          · linarith only [h2497, h2539, hlam]
                                          · linarith only [h2003, h2539, hlam]
                                        · linarith only [h2538, hlam, p2504_0]
                                      · linarith only [h1652, h2537, hlam]
                                    · linarith only [h0, h2536, hlam]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2493, hlam, p2504_1]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2495, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2071, h2489, h2496, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2504_1, u3ehi2]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  rcases p2504_3 (m.d 0 1) (by simp) with h2549 | h2549
                                  · linarith only [h2549, hlam, p2504_0]
                                  · rcases p2504_3 (m.d 1 2) (by simp) with h2551 | h2551
                                    · rcases p2504_3 (m.d 1 3) (by simp) with h2552 | h2552
                                      · rcases p2504_3 (m.d 1 4) (by simp) with h2553 | h2553
                                        · rcases p2504_3 (m.d 1 5) (by simp) with h2554 | h2554
                                          · rcases h5bigk with h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2003, hlam, p2555_1]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2489, h2500, h2503, hc34, hlam, hphi, p2555_1, u3ehi2]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2489, hlam, p2555_1]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2489, h2492, h2495, h2503, hc12, hlam, hphi, ht01, ht0b, ht5b, p2555_1, u5ehi4]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              rcases p2555_3 (m.d 0 5) (by simp) with h2561 | h2561
                                              · linarith only [h2003, h2561, hlam]
                                              · rcases p2555_3 (m.d 1 5) (by simp) with h2563 | h2563
                                                · rcases p2555_3 (m.d 2 5) (by simp) with h2564 | h2564
                                                  · linarith only [h2494, h2564, hlam]
                                                  · rcases p2555_3 (m.d 3 5) (by simp) with h2566 | h2566
                                                    · linarith only [h2496, h2566, hlam]
                                                    · linarith only [h2489, h2566, hlam]
                                                · linarith only [h2003, h2563, hlam]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              rcases p2555_3 (m.d 0 5) (by simp) with h2571 | h2571
                                              · linarith only [h2003, h2571, hlam]
                                              · linarith only [h2073, h2571, hlam]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2071, h2489, h2492, h2495, h2497, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2555_1, u3ehi2]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              rcases p2555_3 (m.d 0 5) (by simp) with h2575 | h2575
                                              · linarith only [h2003, h2575, hlam]
                                              · linarith only [h2491, h2575, hlam]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2073, hlam, p2555_1]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2494, hlam, p2555_1]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2500, hlam, p2555_1]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h0, h2073, hc12, hlam, hphi, ht01, ht0b, ht5b, p2555_1, u5ehi4]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2071, h2489, h2503, hc34, hlam, hphi, p2555_1, u3ehi2]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2496, hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2492, h2495, h2503, hc12, hlam, hphi, ht01, ht0b, ht5b, p2555_1, u5ehi2]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2492, h2495, h2503, hc12, hlam, hphi, ht01, ht0b, ht5b, p2555_1, u5ehi4]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2491, hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2497, hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2502, hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [h2503, hlam, p2555_0]
                                            · have p2555_0 := h2555c.1
                                              have p2555_1 := h2555c.2.1
                                              have p2555_2 := h2555c.2.2.1
                                              have p2555_3 := h2555c.2.2.2
                                              linarith only [hlam, p2555_0]
                                          · linarith only [h2554, hlam, p2504_0]
                                        · linarith only [h1842, h2553, hlam]
                                      · linarith only [h1652, h2552, hlam]
                                    · linarith only [h0, h2551, hlam]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2494, hlam, p2504_1]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2496, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [h2497, hlam, p2504_0]
                                · have p2504_0 := h2504c.1
                                  have p2504_1 := h2504c.2.1
                                  have p2504_2 := h2504c.2.2.1
                                  have p2504_3 := h2504c.2.2.2
                                  linarith only [hlam, p2504_0]
                              · linarith only [h0, h2072, h2502, h2503, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h2074, h2491, h2492, h2495, h2498, h2502, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1842, h2074, h2491, h2492, h2495, h2497, hc01, hc12, hlam, hphi]
                    · linarith only [h2074, h2491, h2495, h2496, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2605 | h2605
                    · linarith only [h2495, h2605, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2607 | h2607
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2608 | h2608
                        · linarith only [h2071, h2495, h2608, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2610 | h2610
                          · linarith only [h1652, h2605, h2610, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2612 | h2612
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2613 | h2613
                              · rcases h1bigk with h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h0, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1652, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1842, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2003, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 1) (by simp) with h2620 | h2620
                                  · linarith only [h2620, hlam, p2614_0]
                                  · rcases p2614_3 (m.d 1 2) (by simp) with h2622 | h2622
                                    · rcases p2614_3 (m.d 1 3) (by simp) with h2623 | h2623
                                      · linarith only [h2492, h2623, hlam]
                                      · linarith only [h1652, h2623, hlam]
                                    · linarith only [h2622, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1652, hc01, hc12, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1842, h2072, h2612, hc12, hlam, hphi, ht01, ht0b, ht5b, p2614_1, u5ehi4]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1652, h2605, hc01, hc12, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2605, h2613, hc01, hc34, hlam, hphi, ht12, ht23, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2492, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2495, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2605, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 1) (by simp) with h2636 | h2636
                                  · linarith only [h2636, hlam, p2614_0]
                                  · rcases p2614_3 (m.d 1 2) (by simp) with h2638 | h2638
                                    · rcases p2614_3 (m.d 1 3) (by simp) with h2639 | h2639
                                      · linarith only [h2495, h2639, hlam]
                                      · linarith only [h1652, h2639, hlam]
                                    · linarith only [h0, h2638, hlam]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2493, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1652, hc01, hc14, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1652, h2605, hc01, hc14, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 1) (by simp) with h2647 | h2647
                                  · linarith only [h2647, hlam, p2614_0]
                                  · rcases p2614_3 (m.d 1 2) (by simp) with h2649 | h2649
                                    · rcases p2614_3 (m.d 1 3) (by simp) with h2650 | h2650
                                      · linarith only [h2605, h2650, hlam]
                                      · linarith only [h1652, h2650, hlam]
                                    · linarith only [h0, h2649, hlam]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2494, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1652, hc01, hc15, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2607, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                              · linarith only [h1842, h2495, h2612, h2613, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h2074, h2491, h2608, h2612, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1842, h2491, h2607, hlam]
                · linarith only [h0, h2073, h2494, hlam]
              · linarith only [h0, h2072, h2493, hlam]
            · linarith only [h0, h2071, h2492, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2664 | h2664
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2665 | h2665
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2666 | h2666
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2667 | h2667
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2668 | h2668
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2669 | h2669
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2670 | h2670
                        · linarith only [h2071, h2074, h2670, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2672 | h2672
                          · linarith only [h2071, h2074, h2491, h2664, h2667, h2669, h2672, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2674 | h2674
                            · linarith only [h2071, h2072, h2074, h2491, h2674, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2676 | h2676
                              · linarith only [h2071, h2074, h2491, h2676, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h2071, h2074, h2669, h2676, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h2071, h2074, h2667, h2669, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h2071, h2074, h2667, h2668, hc35, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2681 | h2681
                    · linarith only [h2667, h2681, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2683 | h2683
                      · linarith only [h2071, h2074, h2491, h2667, h2683, hc34, hlam, hphi, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2685 | h2685
                        · linarith only [h1652, h2071, h2667, h2683, h2685, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2687 | h2687
                          · linarith only [h1652, h2071, h2667, h2683, h2687, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2689 | h2689
                            · linarith only [h1842, h2072, h2683, h2689, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2691 | h2691
                              · linarith only [h1652, h2667, h2683, h2691, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h2071, h2074, h2691, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h2073, h2666, hlam]
              · linarith only [h0, h2072, h2665, hlam]
            · linarith only [h0, h2071, h2073, h2074, h2664, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2697 | h2697
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2698 | h2698
        · linarith only [h2071, h2073, h2698, hlam]
        · linarith only [h2697, h2698, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2701 | h2701
        · linarith only [h2697, h2701, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2703 | h2703
          · linarith only [h2072, h2073, h2703, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2705 | h2705
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2706 | h2706
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2707 | h2707
                · linarith only [h2071, h2073, h2707, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2709 | h2709
                  · linarith only [h2697, h2705, h2707, h2709, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2711 | h2711
                    · linarith only [h2071, h2073, h2701, h2709, h2711, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2713 | h2713
                      · linarith only [h1842, h2703, h2706, h2707, h2713, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2715 | h2715
                        · linarith only [h0, h2071, h2707, h2715, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2717 | h2717
                          · linarith only [h0, h2072, h2707, h2715, h2717, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · linarith only [h0, h2072, h2707, h2715, h2717, hc35, hlam, hphi, u3ehi2]
              · linarith only [h0, h2072, h2706, hlam]
            · linarith only [h0, h2071, h2705, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2722 | h2722
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2723 | h2723
      · linarith only [h2071, h2072, h2723, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2725 | h2725
        · linarith only [h2723, h2725, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2727 | h2727
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2728 | h2728
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2729 | h2729
              · linarith only [h2072, h2722, h2729, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2731 | h2731
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2732 | h2732
                  · linarith only [h2723, h2728, h2729, h2732, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2734 | h2734
                    · linarith only [h2071, h2725, h2732, h2734, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2736 | h2736
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2737 | h2737
                        · linarith only [h2071, h2732, h2737, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h2071, h2729, h2737, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1842, h2727, h2736, hlam]
                · linarith only [h0, h2722, h2731, hlam]
            · linarith only [h0, h2071, h2728, hlam]
          · linarith only [h2071, h2072, h2727, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2744 | h2744
      · linarith only [h2071, h2072, h2744, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2746 | h2746
        · linarith only [h2744, h2746, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2748 | h2748
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2749 | h2749
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2750 | h2750
              · linarith only [h2071, h2072, h2750, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2752 | h2752
                · linarith only [h2071, h2722, h2750, h2752, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2754 | h2754
                  · linarith only [h2744, h2749, h2750, h2754, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2756 | h2756
                    · linarith only [h2071, h2722, h2746, h2754, h2756, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2758 | h2758
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2759 | h2759
                        · linarith only [h2071, h2754, h2759, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h2071, h2750, h2759, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1842, h2748, h2758, hlam]
            · linarith only [h0, h2071, h2749, hlam]
          · linarith only [h2071, h2072, h2748, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
