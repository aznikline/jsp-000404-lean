import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h2067 | h2067
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2068 | h2068
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2069 | h2069
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2070 | h2070
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2071 | h2071
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2072 | h2072
            · linarith only [h1, h2072, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2074 | h2074
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2075 | h2075
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2076 | h2076
                  · linarith only [h1, h2069, h2076, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2078 | h2078
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2079 | h2079
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2080 | h2080
                        · rcases h1bigk with h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2070, h2076, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2069, h2078, h2080, hc01, hc45, hlam, hphi, ht0b, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2069, h2072, h2078, h2080, hc01, hc45, hlam, hphi, ht0b, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            rcases p2081_3 (m.d 0 1) (by simp) with h2086 | h2086
                            · rcases p2081_3 (m.d 1 2) (by simp) with h2087 | h2087
                              · linarith only [h0, h2087, hlam]
                              · linarith only [h2071, h2087, hlam]
                            · linarith only [h2086, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h0, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2069, h2078, h2080, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h0, h2069, h2072, h2078, h2080, hc01, hc45, hlam, hphi, ht0b, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h1, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2069, hlam, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2072, hlam, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h1, h2071, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2070, hlam, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h0, h2070, h2074, h2080, hc01, hc45, hlam, hphi, ht0b, ht5b, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h3, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2071, hlam, p2081_1]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2074, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [h2075, hlam, p2081_0]
                          · have p2081_0 := h2081c.1
                            have p2081_1 := h2081c.2.1
                            have p2081_2 := h2081c.2.2.1
                            have p2081_3 := h2081c.2.2.2
                            linarith only [hlam, p2081_0]
                        · linarith only [h2068, h2078, h2080, h4, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2, h2075, h2076, h2078, h2079, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2067, h2078, h7, hc23, hc34, hlam, hphi]
                · linarith only [h2072, h2074, h2075, hlam]
              · linarith only [h2067, h2074, h7, hc13, hc34, hlam, hphi]
          · linarith only [h2067, h2069, h2071, h6, h7, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2117 | h2117
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2118 | h2118
            · linarith only [h1, h2067, h2118, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2120 | h2120
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2121 | h2121
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2122 | h2122
                  · linarith only [h2069, h2070, h2122, h5, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2124 | h2124
                    · linarith only [h0, h2069, h2070, h2124, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2067, h2124, h7, hc23, hc34, hlam, hphi]
                · linarith only [h2067, h2068, h2069, h2070, h2121, h7, hc23, hc34, hlam, hphi]
              · linarith only [h2067, h2120, h7, hc13, hc34, hlam, hphi]
          · linarith only [h2067, h2069, h2117, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2130 | h2130
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2131 | h2131
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2132 | h2132
            · linarith only [h2067, h2069, h2132, h4, h7, hc02, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h2069, h2130, h2132, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2135 | h2135
            · linarith only [h2067, h2130, h2131, h2135, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h2069, h2130, h2135, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2138 | h2138
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2139 | h2139
            · linarith only [h2069, h2138, h2139, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2141 | h2141
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2142 | h2142
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2143 | h2143
                  · linarith only [h2143, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2145 | h2145
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2146 | h2146
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2147 | h2147
                        · rcases h1bigk with h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2138, h2145, h2147, hc01, hc45, hlam, hphi, ht0b, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2069, h2138, h2145, h2147, hc01, hc45, hlam, hphi, ht0b, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2069, h2138, h2139, h2145, h2147, hc01, hc45, hlam, hphi, ht0b, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            rcases p2148_3 (m.d 0 1) (by simp) with h2153 | h2153
                            · rcases p2148_3 (m.d 1 2) (by simp) with h2154 | h2154
                              · linarith only [h0, h2154, hlam]
                              · linarith only [h2138, h2154, hlam]
                            · linarith only [h2153, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h0, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2069, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2130, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2069, h2138, h2145, h2147, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h1, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2139, hlam, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2069, h2138, h2145, h2147, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2069, h2130, h2138, h2145, h2147, h4, h5, h7, hc02, hc13, hc34, hc45, hlam, hphi, ht0b, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h0, h2130, h2138, h2145, h2147, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h3, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2138, hlam, p2148_1]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2141, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [h2142, hlam, p2148_0]
                          · have p2148_0 := h2148c.1
                            have p2148_1 := h2148c.2.1
                            have p2148_2 := h2148c.2.2.1
                            have p2148_3 := h2148c.2.2.2
                            linarith only [hlam, p2148_0]
                        · linarith only [h2069, h2147, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h2067, h2068, h2130, h2138, h2145, h2146, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h2067, h2069, h2145, h7, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2069, h2138, h2139, h2142, hlam]
              · linarith only [h2067, h2069, h2138, h2141, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2183 | h2183
            · linarith only [h1, h2067, h2183, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2185 | h2185
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2186 | h2186
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2187 | h2187
                  · linarith only [h2187, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2189 | h2189
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2190 | h2190
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2191 | h2191
                        · rcases h1bigk with h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            rcases p2192_3 (m.d 0 1) (by simp) with h2194 | h2194
                            · rcases p2192_3 (m.d 1 2) (by simp) with h2195 | h2195
                              · linarith only [h2195, hlam, p2192_0]
                              · rcases p2192_3 (m.d 1 3) (by simp) with h2197 | h2197
                                · linarith only [h1, h2197, hlam]
                                · linarith only [h2069, h2197, hlam]
                            · linarith only [h2194, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2185, h2191, hc01, hc45, hlam, hphi, ht0b, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2183, h2185, h2191, hc01, hc45, hlam, hphi, ht0b, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            rcases p2192_3 (m.d 0 1) (by simp) with h2203 | h2203
                            · rcases p2192_3 (m.d 1 2) (by simp) with h2204 | h2204
                              · linarith only [h0, h2204, hlam]
                              · rcases p2192_3 (m.d 1 3) (by simp) with h2206 | h2206
                                · linarith only [h1, h2206, hlam]
                                · linarith only [h2185, h2206, hlam]
                            · linarith only [h2203, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h0, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2069, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2130, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2138, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h1, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2183, hlam, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2069, h4, h7, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h0, h2130, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h0, h2130, h2138, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h3, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2192_1]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2185, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [h2186, hlam, p2192_0]
                          · have p2192_0 := h2192c.1
                            have p2192_1 := h2192c.2.1
                            have p2192_2 := h2192c.2.2.1
                            have p2192_3 := h2192c.2.2.2
                            linarith only [hlam, p2192_0]
                        · linarith only [h2068, h2191, h7, hlam]
                      · linarith only [h2130, h2186, h2190, hlam]
                    · linarith only [h2069, h2185, h2189, hlam]
                · linarith only [h2183, h2185, h2186, hlam]
              · linarith only [h2067, h2185, h7, hc13, hc34, hlam, hphi]
    · linarith only [h2067, h2068, h7, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2236 | h2236
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2237 | h2237
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2238 | h2238
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2239 | h2239
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2240 | h2240
            · linarith only [h1, h2240, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2242 | h2242
              · linarith only [h1, h2067, h2242, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2244 | h2244
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2245 | h2245
                  · linarith only [h2245, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2247 | h2247
                    · linarith only [h1, h2067, h2237, h2247, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2249 | h2249
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2250 | h2250
                        · rcases h1bigk with h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2238, h2249, hc01, hc45, hlam, hphi, ht0b, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 1) (by simp) with h2254 | h2254
                            · rcases p2251_3 (m.d 1 2) (by simp) with h2255 | h2255
                              · linarith only [h0, h2255, hlam]
                              · linarith only [h2237, h2255, hlam]
                            · linarith only [h2254, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2238, h2249, hc01, hc45, hlam, hphi, ht0b, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 1) (by simp) with h2260 | h2260
                            · rcases p2251_3 (m.d 1 2) (by simp) with h2261 | h2261
                              · linarith only [h0, h2261, hlam]
                              · linarith only [h2239, h2261, hlam]
                            · linarith only [h2260, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, h2238, h2249, hc01, hc45, hlam, hphi, ht0b, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h1, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2237, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2240, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2242, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2238, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2, h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, h2237, h2238, h2242, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h3, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2239, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2237, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2244, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                        · linarith only [h2249, h2250, h5, h7, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2286 | h2286
                        · rcases h1bigk with h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            rcases p2287_3 (m.d 0 1) (by simp) with h2290 | h2290
                            · rcases p2287_3 (m.d 1 2) (by simp) with h2291 | h2291
                              · linarith only [h0, h2291, hlam]
                              · linarith only [h2237, h2291, hlam]
                            · linarith only [h2290, hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2244, h2245, h2249, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2244, h2245, h2249, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h0, hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h0, h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h0, h2244, h2245, h2249, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h1, hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2237, hlam, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2240, hlam, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2242, hlam, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2, hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2238, hlam, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2, h2237, h7, hc23, hc34, hlam, hphi, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h0, h2238, h2239, h2245, h2249, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h3, hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2239, hlam, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2237, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [h2244, hlam, p2287_0]
                          · have p2287_0 := h2287c.1
                            have p2287_1 := h2287c.2.1
                            have p2287_2 := h2287c.2.2.1
                            have p2287_3 := h2287c.2.2.2
                            linarith only [hlam, p2287_0]
                        · linarith only [h2236, h2286, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2318 | h2318
                  · linarith only [h2236, h2237, h2240, h2244, h2318, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2320 | h2320
                    · linarith only [h1, h2067, h2237, h2320, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2322 | h2322
                      · linarith only [h2238, h2244, h2322, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2324 | h2324
                        · rcases h1bigk with h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2328 | h2328
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2329 | h2329
                              · linarith only [h0, h2329, hlam]
                              · linarith only [h2237, h2329, hlam]
                            · linarith only [h2328, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2333 | h2333
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2334 | h2334
                              · linarith only [h0, h2334, hlam]
                              · linarith only [h2238, h2334, hlam]
                            · linarith only [h2333, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2338 | h2338
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2339 | h2339
                              · linarith only [h0, h2339, hlam]
                              · linarith only [h2239, h2339, hlam]
                            · linarith only [h2338, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h0, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h0, h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h0, h2238, h2318, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h1, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2237, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2240, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2242, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2238, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2236, h2237, h2244, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2244, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h3, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2239, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2237, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2236, h2244, h7, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                        · linarith only [h2236, h2324, h7, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2364 | h2364
            · linarith only [h1, h2364, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2366 | h2366
              · linarith only [h2067, h2236, h2238, h2239, h2364, h2366, h6, h7, hc03, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2368 | h2368
                · linarith only [h2238, h2239, h2368, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2370 | h2370
                  · linarith only [h1, h2236, h2237, h2368, h2370, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2372 | h2372
                    · linarith only [h1, h2067, h2237, h2372, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2374 | h2374
                      · linarith only [h2238, h2239, h2368, h2374, hlam]
                      · linarith only [h2236, h2238, h2239, h2370, h2374, h7, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2377 | h2377
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2378 | h2378
            · linarith only [h1, h2237, h2238, h2378, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2380 | h2380
              · linarith only [h2067, h2237, h2238, h2380, h5, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2382 | h2382
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2383 | h2383
                  · linarith only [h1, h2237, h2383, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2385 | h2385
                    · linarith only [h0, h2067, h2237, h2238, h2385, h5, hc01, hc05, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2387 | h2387
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2388 | h2388
                        · rcases h1bigk with h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2377, h2385, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            rcases p2389_3 (m.d 0 1) (by simp) with h2392 | h2392
                            · rcases p2389_3 (m.d 1 2) (by simp) with h2393 | h2393
                              · linarith only [h0, h2393, hlam]
                              · linarith only [h2237, h2393, hlam]
                            · linarith only [h2392, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2238, h2377, h2385, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            rcases p2389_3 (m.d 0 1) (by simp) with h2398 | h2398
                            · rcases p2389_3 (m.d 1 2) (by simp) with h2399 | h2399
                              · linarith only [h0, h2399, hlam]
                              · linarith only [h2377, h2399, hlam]
                            · linarith only [h2398, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2238, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, h2237, h2238, h2380, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h1, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2237, hlam, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2378, hlam, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2380, hlam, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, h2238, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, h2237, h2238, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h0, h2237, h2238, h2380, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h3, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2377, hlam, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2237, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [h2382, hlam, p2389_0]
                          · have p2389_0 := h2389c.1
                            have p2389_1 := h2389c.2.1
                            have p2389_2 := h2389c.2.2.1
                            have p2389_3 := h2389c.2.2.2
                            linarith only [hlam, p2389_0]
                        · linarith only [h2236, h2388, h7, hlam]
                      · linarith only [h2238, h2377, h2382, h2387, hlam]
                · linarith only [h2236, h2237, h2238, h2382, h7, hc23, hc34, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2426 | h2426
            · linarith only [h1, h2237, h2238, h2426, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2428 | h2428
              · linarith only [h1, h2067, h2428, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2430 | h2430
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2431 | h2431
                  · linarith only [h1, h2237, h2431, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2433 | h2433
                    · linarith only [h2067, h2237, h2377, h2433, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2435 | h2435
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2436 | h2436
                        · rcases h1bigk with h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2237, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            rcases p2437_3 (m.d 0 1) (by simp) with h2440 | h2440
                            · rcases p2437_3 (m.d 1 2) (by simp) with h2441 | h2441
                              · linarith only [h0, h2441, hlam]
                              · linarith only [h2237, h2441, hlam]
                            · linarith only [h2440, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2237, h2377, h2430, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2237, h2377, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2238, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2377, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2237, hlam, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2426, hlam, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2428, hlam, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, h2238, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, h2237, h2238, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, h2238, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h3, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2237, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, h2237, h2377, h2435, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2430, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                        · linarith only [h2238, h2430, h2436, h5, h7, hlam]
                      · linarith only [h2238, h2430, h2435, hlam]
                · linarith only [h2236, h2237, h2238, h2430, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2470 | h2470
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2471 | h2471
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2472 | h2472
            · linarith only [h2237, h2470, h2472, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h2237, h2470, h2472, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2475 | h2475
            · linarith only [h2237, h2470, h2475, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h2237, h2470, h2475, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2478 | h2478
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2479 | h2479
            · linarith only [h2237, h2478, h2479, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2481 | h2481
              · linarith only [h2067, h2237, h2481, h4, hlam]
              · linarith only [h2237, h2478, h2481, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2484 | h2484
            · linarith only [h1, h2484, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2486 | h2486
              · linarith only [h2067, h2237, h2486, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2488 | h2488
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2489 | h2489
                  · linarith only [h2489, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2491 | h2491
                    · linarith only [h2067, h2491, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2493 | h2493
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2494 | h2494
                        · rcases h1bigk with h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 1) (by simp) with h2497 | h2497
                            · rcases p2495_3 (m.d 1 2) (by simp) with h2498 | h2498
                              · linarith only [h2498, hlam, p2495_0]
                              · rcases p2495_3 (m.d 1 3) (by simp) with h2500 | h2500
                                · linarith only [h1, h2500, hlam]
                                · linarith only [h2237, h2500, hlam]
                            · linarith only [h2497, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 1) (by simp) with h2504 | h2504
                            · rcases p2495_3 (m.d 1 2) (by simp) with h2505 | h2505
                              · linarith only [h0, h2505, hlam]
                              · rcases p2495_3 (m.d 1 3) (by simp) with h2507 | h2507
                                · linarith only [h2507, hlam, p2495_0]
                                · rcases p2495_3 (m.d 1 4) (by simp) with h2509 | h2509
                                  · linarith only [h2, h2509, hlam]
                                  · linarith only [h2484, h2509, hlam]
                            · linarith only [h2504, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2488, hc01, hc45, hlam, hphi, ht0b, ht5b, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 1) (by simp) with h2514 | h2514
                            · rcases p2495_3 (m.d 1 2) (by simp) with h2515 | h2515
                              · linarith only [h0, h2515, hlam]
                              · rcases p2495_3 (m.d 1 3) (by simp) with h2517 | h2517
                                · linarith only [h1, h2517, hlam]
                                · rcases p2495_3 (m.d 1 4) (by simp) with h2519 | h2519
                                  · linarith only [h2, h2519, hlam]
                                  · linarith only [h2488, h2519, hlam]
                            · linarith only [h2514, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h0, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2237, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2470, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2478, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2484, hlam, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2486, hlam, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2470, h5, h7, hc13, hc34, hlam, hphi, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h0, h2237, h2470, h2486, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h3, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h0, h2237, h2478, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2488, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                        · linarith only [h2236, h2494, h7, hlam]
                      · linarith only [h2470, h2488, h2493, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2545 | h2545
                  · linarith only [h2236, h2237, h2484, h2488, h2545, h7, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2547 | h2547
                    · linarith only [h2067, h2547, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2549 | h2549
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2550 | h2550
                        · rcases h1bigk with h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c | h2551c
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            rcases p2551_3 (m.d 0 1) (by simp) with h2553 | h2553
                            · rcases p2551_3 (m.d 1 2) (by simp) with h2554 | h2554
                              · linarith only [h2554, hlam, p2551_0]
                              · rcases p2551_3 (m.d 1 3) (by simp) with h2556 | h2556
                                · linarith only [h1, h2556, hlam]
                                · linarith only [h2237, h2556, hlam]
                            · linarith only [h2553, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            rcases p2551_3 (m.d 0 1) (by simp) with h2560 | h2560
                            · rcases p2551_3 (m.d 1 2) (by simp) with h2561 | h2561
                              · linarith only [h0, h2561, hlam]
                              · rcases p2551_3 (m.d 1 3) (by simp) with h2563 | h2563
                                · linarith only [h2563, hlam, p2551_0]
                                · rcases p2551_3 (m.d 1 4) (by simp) with h2565 | h2565
                                  · linarith only [h2, h2565, hlam]
                                  · linarith only [h2484, h2565, hlam]
                            · linarith only [h2560, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            rcases p2551_3 (m.d 0 1) (by simp) with h2569 | h2569
                            · rcases p2551_3 (m.d 1 2) (by simp) with h2570 | h2570
                              · linarith only [h0, h2570, hlam]
                              · rcases p2551_3 (m.d 1 3) (by simp) with h2572 | h2572
                                · linarith only [h1, h2572, hlam]
                                · rcases p2551_3 (m.d 1 4) (by simp) with h2574 | h2574
                                  · linarith only [h2574, hlam, p2551_0]
                                  · rcases p2551_3 (m.d 1 5) (by simp) with h2576 | h2576
                                    · linarith only [h2576, h3, hlam]
                                    · linarith only [h2488, h2576, hlam]
                            · linarith only [h2569, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            rcases p2551_3 (m.d 0 1) (by simp) with h2580 | h2580
                            · rcases p2551_3 (m.d 1 2) (by simp) with h2581 | h2581
                              · linarith only [h0, h2581, hlam]
                              · rcases p2551_3 (m.d 1 3) (by simp) with h2583 | h2583
                                · linarith only [h1, h2583, hlam]
                                · rcases p2551_3 (m.d 1 4) (by simp) with h2585 | h2585
                                  · linarith only [h2, h2585, hlam]
                                  · rcases p2551_3 (m.d 1 5) (by simp) with h2587 | h2587
                                    · linarith only [h2587, hlam, p2551_0]
                                    · rcases h1emin with h2589 | h2589 | h2589 | h2589 | h2589
                                      · rcases h5bigk with h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          rcases p2590_3 (m.d 0 5) (by simp) with h2592 | h2592
                                          · rcases p2590_3 (m.d 1 5) (by simp) with h2593 | h2593
                                            · linarith only [h2593, h3, hlam]
                                            · rcases p2590_3 (m.d 2 5) (by simp) with h2595 | h2595
                                              · linarith only [h2595, h6, hlam]
                                              · linarith only [h2478, h2595, hlam]
                                          · linarith only [h2592, h3, hlam]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2236, h2237, h2547, h7, hc12, hc34, hlam, hphi, ht23, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2067, hlam, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2236, h2237, h2484, h2488, h7, hc12, hc34, hlam, hphi, ht23, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h3, hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2478, hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2486, hlam, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2488, hlam, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h6, hlam, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          rcases p2590_3 (m.d 0 5) (by simp) with h2608 | h2608
                                          · rcases p2590_3 (m.d 1 5) (by simp) with h2609 | h2609
                                            · linarith only [h2478, h2609, hlam]
                                            · rcases p2590_3 (m.d 2 5) (by simp) with h2611 | h2611
                                              · rcases p2590_3 (m.d 3 5) (by simp) with h2612 | h2612
                                                · rcases p2590_3 (m.d 4 5) (by simp) with h2613 | h2613
                                                  · linarith only [h2549, h2613, hlam]
                                                  · linarith only [h2488, h2613, hlam]
                                                · linarith only [h2486, h2612, hlam]
                                              · linarith only [h2478, h2611, hlam]
                                          · linarith only [h2608, h3, hlam]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2547, hlam, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h0, h2237, h2484, h2488, h2549, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2067, h2237, h2550, h4, hc12, hc34, hlam, hphi, ht23, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          rcases p2590_3 (m.d 0 5) (by simp) with h2623 | h2623
                                          · linarith only [h2067, h2623, hlam]
                                          · linarith only [h2623, h3, hlam]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2237, h2484, h2488, h2549, h2550, hc12, hc34, hlam, hphi, ht23, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2237, h2484, h2488, h2550, hc12, hc34, hlam, hphi, ht23, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2236, hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2236, h2237, h2484, h2488, h7, hc12, hc34, hlam, hphi, ht23, p2590_1]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2549, hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [h2550, hlam, p2590_0]
                                        · have p2590_0 := h2590c.1
                                          have p2590_1 := h2590c.2.1
                                          have p2590_2 := h2590c.2.2.1
                                          have p2590_3 := h2590c.2.2.2
                                          linarith only [hlam, p2590_0]
                                      · linarith only [h2237, h2589, hc23, hlam, ht12]
                                      · linarith only [h2484, h2488, h2589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2551_1]
                                      · linarith only [h2488, h2589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2551_1]
                                      · linarith only [h2589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2551_1]
                            · linarith only [h2580, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h0, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2237, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2470, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2478, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h1, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2484, hlam, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2486, hlam, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h0, h2470, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2488, hlam, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h3, hlam, p2551_0]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h0, h2478, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h0, h2237, h2478, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [h2236, h2488, h7, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2551_1]
                          · have p2551_0 := h2551c.1
                            have p2551_1 := h2551c.2.1
                            have p2551_2 := h2551c.2.2.1
                            have p2551_3 := h2551c.2.2.2
                            linarith only [hlam, p2551_0]
                        · linarith only [h2549, h2550, h5, h7, hlam]
                      · linarith only [h2236, h2470, h2549, h7, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2661 | h2661
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2662 | h2662
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2663 | h2663
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2664 | h2664
            · linarith only [h1, h2664, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2666 | h2666
              · linarith only [h1, h2067, h2666, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2668 | h2668
                · linarith only [h2, h2236, h2668, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2670 | h2670
                  · linarith only [h1, h2661, h2670, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2672 | h2672
                    · linarith only [h1, h2067, h2661, h2672, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2674 | h2674
                      · linarith only [h0, h2, h2236, h2662, h2674, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2676 | h2676
                        · rcases h1bigk with h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c | h2677c
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2663, hc01, hc25, hlam, hphi, ht0b, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            rcases p2677_3 (m.d 0 1) (by simp) with h2680 | h2680
                            · rcases p2677_3 (m.d 1 2) (by simp) with h2681 | h2681
                              · linarith only [h0, h2681, hlam]
                              · linarith only [h2661, h2681, hlam]
                            · linarith only [h2680, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            rcases p2677_3 (m.d 0 1) (by simp) with h2685 | h2685
                            · rcases p2677_3 (m.d 1 2) (by simp) with h2686 | h2686
                              · linarith only [h0, h2686, hlam]
                              · linarith only [h2662, h2686, hlam]
                            · linarith only [h2685, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            rcases p2677_3 (m.d 0 1) (by simp) with h2690 | h2690
                            · rcases p2677_3 (m.d 1 2) (by simp) with h2691 | h2691
                              · linarith only [h0, h2691, hlam]
                              · linarith only [h2663, h2691, hlam]
                            · linarith only [h2690, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h0, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h0, h2661, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h1, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2661, hlam, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2664, hlam, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2666, hlam, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2662, hlam, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2, h2661, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2668, hlam, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h3, hlam, p2677_0]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2663, hlam, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2661, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [h2236, h2676, h3, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2677_1]
                          · have p2677_0 := h2677c.1
                            have p2677_1 := h2677c.2.1
                            have p2677_2 := h2677c.2.2.1
                            have p2677_3 := h2677c.2.2.2
                            linarith only [hlam, p2677_0]
                        · rcases h1bigk with h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2661, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            rcases p2715_3 (m.d 0 1) (by simp) with h2718 | h2718
                            · rcases p2715_3 (m.d 1 2) (by simp) with h2719 | h2719
                              · linarith only [h0, h2719, hlam]
                              · linarith only [h2661, h2719, hlam]
                            · linarith only [h2718, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            rcases p2715_3 (m.d 0 1) (by simp) with h2723 | h2723
                            · rcases p2715_3 (m.d 1 2) (by simp) with h2724 | h2724
                              · linarith only [h0, h2724, hlam]
                              · linarith only [h2662, h2724, hlam]
                            · linarith only [h2723, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            rcases p2715_3 (m.d 0 1) (by simp) with h2728 | h2728
                            · rcases p2715_3 (m.d 1 2) (by simp) with h2729 | h2729
                              · linarith only [h0, h2729, hlam]
                              · linarith only [h2663, h2729, hlam]
                            · linarith only [h2728, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h0, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h1, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2661, hlam, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2664, hlam, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2666, hlam, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2662, hlam, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2, h2661, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2668, hlam, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h3, hlam, p2715_0]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2663, hlam, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h2661, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2715_1]
                          · have p2715_0 := h2715c.1
                            have p2715_1 := h2715c.2.1
                            have p2715_2 := h2715c.2.2.1
                            have p2715_3 := h2715c.2.2.2
                            linarith only [hlam, p2715_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2753 | h2753
            · linarith only [h1, h2753, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2755 | h2755
              · linarith only [h1, h2067, h2755, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2757 | h2757
                · linarith only [h2, h2236, h2757, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2759 | h2759
                  · linarith only [h0, h2661, h2663, h2759, h6, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2761 | h2761
                    · linarith only [h2067, h2662, h2663, h2759, h2761, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2763 | h2763
                      · linarith only [h0, h2662, h2663, h2763, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2765 | h2765
                        · linarith only [h2236, h2662, h2663, h2759, h2765, h6, hc23, hc34, hlam, hphi]
                        · rcases h1bigk with h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2662, h2759, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            rcases p2767_3 (m.d 0 1) (by simp) with h2770 | h2770
                            · rcases p2767_3 (m.d 1 2) (by simp) with h2771 | h2771
                              · linarith only [h0, h2771, hlam]
                              · linarith only [h2661, h2771, hlam]
                            · linarith only [h2770, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            rcases p2767_3 (m.d 0 1) (by simp) with h2775 | h2775
                            · rcases p2767_3 (m.d 1 2) (by simp) with h2776 | h2776
                              · linarith only [h0, h2776, hlam]
                              · linarith only [h2662, h2776, hlam]
                            · linarith only [h2775, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2662, h2663, h2759, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h0, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2661, h2663, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2067, h2663, h2765, h6, hc14, hc45, hlam, hphi, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2663, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h1, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2661, hlam, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2753, hlam, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2755, hlam, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2662, hlam, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2, h2661, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2757, hlam, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h3, hlam, p2767_0]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2662, h2759, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2067, h2661, h2663, h2765, h6, hc23, hc45, hlam, hphi, ht34, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [h2067, h2663, h2765, h6, hc14, hc45, hlam, hphi, p2767_1]
                          · have p2767_0 := h2767c.1
                            have p2767_1 := h2767c.2.1
                            have p2767_2 := h2767c.2.2.1
                            have p2767_3 := h2767c.2.2.2
                            linarith only [hlam, p2767_0]
        · linarith only [h2236, h2661, h2662, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2802 | h2802
        · linarith only [h2236, h2661, h2802, h4, h7, hc24, hc45, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2804 | h2804
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2805 | h2805
            · linarith only [h2661, h2804, h2805, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2807 | h2807
              · linarith only [h1, h2067, h2807, hlam]
              · linarith only [h2661, h2804, h2807, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2810 | h2810
            · linarith only [h1, h2810, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2812 | h2812
              · linarith only [h2067, h2661, h2812, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2814 | h2814
                · linarith only [h2236, h2802, h2814, h5, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2816 | h2816
                  · linarith only [h2816, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2818 | h2818
                    · linarith only [h2067, h2818, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2820 | h2820
                      · linarith only [h2236, h2820, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2822 | h2822
                        · linarith only [h2236, h2661, h2822, h4, h7, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h2661, h2822, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_21_15_H_I_L_I_s6_x0 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_21_15_H_I_L_I_s6_x1 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

end R2N4
