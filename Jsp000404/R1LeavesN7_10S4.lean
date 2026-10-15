import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 3 (by decide) (by decide) with h2106 | h2106
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2107 | h2107
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2108 | h2108
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2109 | h2109
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2110 | h2110
          · linarith only [h1, h2110, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2112 | h2112
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2113 | h2113
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2114 | h2114
                · linarith only [h0, h2106, h2112, h2114, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2116 | h2116
                  · linarith only [h1, h2107, h2112, h2116, h6, hlam]
                  · rcases h2bigk with h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c | h2118c
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h0, h2106, h2113, hc01, hc35, hlam, hphi, ht0b, ht5b, p2118_1]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      rcases p2118_3 (m.d 0 2) (by simp) with h2121 | h2121
                      · rcases p2118_3 (m.d 1 2) (by simp) with h2122 | h2122
                        · linarith only [h0, h2122, hlam]
                        · linarith only [h2106, h2122, hlam]
                      · linarith only [h2121, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      rcases p2118_3 (m.d 0 2) (by simp) with h2126 | h2126
                      · rcases p2118_3 (m.d 1 2) (by simp) with h2127 | h2127
                        · linarith only [h0, h2127, hlam]
                        · linarith only [h2107, h2127, hlam]
                      · linarith only [h2126, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      rcases p2118_3 (m.d 0 2) (by simp) with h2131 | h2131
                      · rcases p2118_3 (m.d 1 2) (by simp) with h2132 | h2132
                        · linarith only [h0, h2132, hlam]
                        · linarith only [h2108, h2132, hlam]
                      · linarith only [h2131, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h0, hlam, p2118_1]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h0, h2113, h2116, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2118_1]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      rcases p2118_3 (m.d 0 2) (by simp) with h2139 | h2139
                      · rcases p2118_3 (m.d 1 2) (by simp) with h2140 | h2140
                        · rcases p2118_3 (m.d 2 3) (by simp) with h2141 | h2141
                          · linarith only [h2106, h2141, hlam]
                          · linarith only [h2112, h2141, hlam]
                        · linarith only [h2140, hlam, p2118_0]
                      · linarith only [h2139, h3, hlam]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      rcases p2118_3 (m.d 0 2) (by simp) with h2146 | h2146
                      · rcases p2118_3 (m.d 1 2) (by simp) with h2147 | h2147
                        · rcases p2118_3 (m.d 2 3) (by simp) with h2148 | h2148
                          · linarith only [h2106, h2148, hlam]
                          · linarith only [h2113, h2148, hlam]
                        · linarith only [h2147, hlam, p2118_0]
                      · linarith only [h2146, h4, hlam]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2106, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h0, h2106, h2112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2118_1]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h0, h2106, hc01, hc25, hlam, hphi, ht0b, ht5b, p2118_1]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h3, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2107, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2112, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2114, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h4, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2108, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h2113, hlam, p2118_0]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [h0, h2108, h2112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2118_1]
                    · have p2118_0 := h2118c.1
                      have p2118_1 := h2118c.2.1
                      have p2118_2 := h2118c.2.2.1
                      have p2118_3 := h2118c.2.2.2
                      linarith only [hlam, p2118_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2168 | h2168
                · linarith only [h1, h2107, h2168, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2170 | h2170
                  · linarith only [h2170, h5, h6, hlam]
                  · rcases h2bigk with h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h0, h2106, h2112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      rcases p2172_3 (m.d 0 2) (by simp) with h2175 | h2175
                      · rcases p2172_3 (m.d 1 2) (by simp) with h2176 | h2176
                        · linarith only [h0, h2176, hlam]
                        · linarith only [h2106, h2176, hlam]
                      · linarith only [h2175, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      rcases p2172_3 (m.d 0 2) (by simp) with h2180 | h2180
                      · rcases p2172_3 (m.d 1 2) (by simp) with h2181 | h2181
                        · linarith only [h0, h2181, hlam]
                        · linarith only [h2107, h2181, hlam]
                      · linarith only [h2180, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      rcases p2172_3 (m.d 0 2) (by simp) with h2185 | h2185
                      · rcases p2172_3 (m.d 1 2) (by simp) with h2186 | h2186
                        · linarith only [h0, h2186, hlam]
                        · linarith only [h2108, h2186, hlam]
                      · linarith only [h2185, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h0, hlam, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h0, h2112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      rcases p2172_3 (m.d 0 2) (by simp) with h2193 | h2193
                      · rcases p2172_3 (m.d 1 2) (by simp) with h2194 | h2194
                        · rcases p2172_3 (m.d 2 3) (by simp) with h2195 | h2195
                          · linarith only [h2106, h2195, hlam]
                          · linarith only [h2112, h2195, hlam]
                        · linarith only [h2194, hlam, p2172_0]
                      · linarith only [h2193, h3, hlam]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h0, h2112, h2113, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2106, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2113, h2170, hc24, hc45, hlam, hphi, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2113, hlam, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h3, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2107, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2112, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2168, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h4, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h2108, hlam, p2172_0]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h0, h2112, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [h0, h2108, h2112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2172_1]
                    · have p2172_0 := h2172c.1
                      have p2172_1 := h2172c.2.1
                      have p2172_2 := h2172c.2.2.1
                      have p2172_3 := h2172c.2.2.2
                      linarith only [hlam, p2172_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2216 | h2216
              · linarith only [h0, h2106, h2109, h2112, h2216, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2218 | h2218
                · linarith only [h2218, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2220 | h2220
                  · linarith only [h0, h2106, h2109, h2220, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h2bigk with h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c | h2222c
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2106, h2109, h2112, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      rcases p2222_3 (m.d 0 2) (by simp) with h2225 | h2225
                      · rcases p2222_3 (m.d 1 2) (by simp) with h2226 | h2226
                        · linarith only [h0, h2226, hlam]
                        · linarith only [h2106, h2226, hlam]
                      · linarith only [h2225, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      rcases p2222_3 (m.d 0 2) (by simp) with h2230 | h2230
                      · rcases p2222_3 (m.d 1 2) (by simp) with h2231 | h2231
                        · linarith only [h0, h2231, hlam]
                        · linarith only [h2107, h2231, hlam]
                      · linarith only [h2230, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      rcases p2222_3 (m.d 0 2) (by simp) with h2235 | h2235
                      · rcases p2222_3 (m.d 1 2) (by simp) with h2236 | h2236
                        · linarith only [h0, h2236, hlam]
                        · linarith only [h2108, h2236, hlam]
                      · linarith only [h2235, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h0, hlam, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      rcases p2222_3 (m.d 0 2) (by simp) with h2242 | h2242
                      · rcases p2222_3 (m.d 1 2) (by simp) with h2243 | h2243
                        · rcases p2222_3 (m.d 2 3) (by simp) with h2244 | h2244
                          · linarith only [h2244, hlam, p2222_0]
                          · rcases p2222_3 (m.d 2 4) (by simp) with h2246 | h2246
                            · linarith only [h2107, h2246, hlam]
                            · linarith only [h2112, h2246, hlam]
                        · linarith only [h2243, hlam, p2222_0]
                      · linarith only [h2, h2242, hlam]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      rcases p2222_3 (m.d 0 2) (by simp) with h2251 | h2251
                      · rcases p2222_3 (m.d 1 2) (by simp) with h2252 | h2252
                        · rcases p2222_3 (m.d 2 3) (by simp) with h2253 | h2253
                          · linarith only [h2106, h2253, hlam]
                          · rcases p2222_3 (m.d 2 4) (by simp) with h2255 | h2255
                            · linarith only [h2255, hlam, p2222_0]
                            · rcases p2222_3 (m.d 2 5) (by simp) with h2257 | h2257
                              · linarith only [h2108, h2257, hlam]
                              · linarith only [h2218, h2257, hlam]
                        · linarith only [h2252, hlam, p2222_0]
                      · linarith only [h2251, h3, hlam]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      rcases p2222_3 (m.d 0 2) (by simp) with h2262 | h2262
                      · rcases p2222_3 (m.d 1 2) (by simp) with h2263 | h2263
                        · rcases p2222_3 (m.d 2 3) (by simp) with h2264 | h2264
                          · linarith only [h2106, h2264, hlam]
                          · rcases p2222_3 (m.d 2 4) (by simp) with h2266 | h2266
                            · linarith only [h2107, h2266, hlam]
                            · rcases p2222_3 (m.d 2 5) (by simp) with h2268 | h2268
                              · linarith only [h2268, hlam, p2222_0]
                              · rcases h4bigk with h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2109, h2112, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2112, h6, hc23, hc45, hlam, hphi, ht34, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2112, h6, hc23, hc45, hlam, hphi, ht34, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h6, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h1, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h1, h2112, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h1, h2112, h6, hc23, hc45, hlam, hphi, ht34, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2110, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h3, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2107, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2112, hlam, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2218, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h5, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2109, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2109, h2112, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2220, hlam, p2270_0]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2112, hc23, hc45, hlam, hphi, ht34, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [h2112, hc23, hc45, hlam, hphi, ht34, p2270_1]
                                · have p2270_0 := h2270c.1
                                  have p2270_1 := h2270c.2.1
                                  have p2270_2 := h2270c.2.2.1
                                  have p2270_3 := h2270c.2.2.2
                                  linarith only [hlam, p2270_0]
                        · linarith only [h2263, hlam, p2222_0]
                      · linarith only [h2262, h4, hlam]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2106, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2112, hlam, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2216, hlam, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h3, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2107, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h3, h6, hc23, hc45, hlam, hphi, ht34, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2218, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h4, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h2108, hlam, p2222_0]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h0, h2108, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [h0, h2108, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2222_1]
                    · have p2222_0 := h2222c.1
                      have p2222_1 := h2222c.2.1
                      have p2222_2 := h2222c.2.2.1
                      have p2222_3 := h2222c.2.2.2
                      linarith only [hlam, p2222_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2313 | h2313
          · linarith only [h2109, h2313, h5, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2315 | h2315
            · linarith only [h0, h2106, h2109, h2315, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2317 | h2317
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2318 | h2318
                · linarith only [h2106, h2109, h2317, h2318, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h2315, h2317, h2318, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2321 | h2321
                · linarith only [h0, h2109, h2321, h3, h5, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2323 | h2323
                  · linarith only [h2323, h5, h6, hlam]
                  · rcases h2bigk with h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2327 | h2327
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2328 | h2328
                        · linarith only [h0, h2328, hlam]
                        · rcases p2325_3 (m.d 2 3) (by simp) with h2330 | h2330
                          · linarith only [h2, h2330, hlam]
                          · rcases p2325_3 (m.d 2 4) (by simp) with h2332 | h2332
                            · linarith only [h2332, h3, hlam]
                            · rcases p2325_3 (m.d 2 5) (by simp) with h2334 | h2334
                              · linarith only [h2334, h4, hlam]
                              · rcases h4bigk with h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c | h2336c
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h6, hc14, hc45, hlam, hphi, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2315, h6, hc23, hc45, hlam, hphi, ht34, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2106, h2109, h6, hc23, hc45, hlam, hphi, ht34, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h6, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h1, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h1, h2315, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2109, hlam, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2313, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h3, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2107, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2315, hlam, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2321, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h5, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h0, h2, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2315, h5, h6, hc23, hc45, hlam, hphi, ht34, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2323, hlam, p2336_0]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2107, h2315, hc23, hc45, hlam, hphi, ht34, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2315, hc23, hc45, hlam, hphi, ht34, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [h2106, h2109, hc23, hc45, hlam, hphi, ht34, p2336_1]
                                · have p2336_0 := h2336c.1
                                  have p2336_1 := h2336c.2.1
                                  have p2336_2 := h2336c.2.2.1
                                  have p2336_3 := h2336c.2.2.2
                                  linarith only [hlam, p2336_0]
                      · linarith only [h0, h2327, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2363 | h2363
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2364 | h2364
                        · linarith only [h0, h2364, hlam]
                        · linarith only [h2106, h2364, hlam]
                      · linarith only [h2363, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2368 | h2368
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2369 | h2369
                        · linarith only [h0, h2369, hlam]
                        · linarith only [h2107, h2369, hlam]
                      · linarith only [h2368, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2373 | h2373
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2374 | h2374
                        · linarith only [h0, h2374, hlam]
                        · linarith only [h2108, h2374, hlam]
                      · linarith only [h2373, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h0, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2380 | h2380
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2381 | h2381
                        · rcases p2325_3 (m.d 2 3) (by simp) with h2382 | h2382
                          · linarith only [h2382, hlam, p2325_0]
                          · rcases p2325_3 (m.d 2 4) (by simp) with h2384 | h2384
                            · linarith only [h2107, h2384, hlam]
                            · linarith only [h2315, h2384, hlam]
                        · linarith only [h2381, hlam, p2325_0]
                      · linarith only [h2, h2380, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2389 | h2389
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2390 | h2390
                        · rcases p2325_3 (m.d 2 3) (by simp) with h2391 | h2391
                          · linarith only [h2106, h2391, hlam]
                          · rcases p2325_3 (m.d 2 4) (by simp) with h2393 | h2393
                            · linarith only [h2393, hlam, p2325_0]
                            · rcases p2325_3 (m.d 2 5) (by simp) with h2395 | h2395
                              · linarith only [h2108, h2395, hlam]
                              · linarith only [h2321, h2395, hlam]
                        · linarith only [h2390, hlam, p2325_0]
                      · linarith only [h2389, h3, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 2) (by simp) with h2400 | h2400
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2401 | h2401
                        · rcases p2325_3 (m.d 2 3) (by simp) with h2402 | h2402
                          · linarith only [h2106, h2402, hlam]
                          · rcases p2325_3 (m.d 2 4) (by simp) with h2404 | h2404
                            · linarith only [h2107, h2404, hlam]
                            · rcases p2325_3 (m.d 2 5) (by simp) with h2406 | h2406
                              · linarith only [h2406, hlam, p2325_0]
                              · rcases h4bigk with h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2107, h2315, h6, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2315, h6, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2106, h2109, h6, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h6, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h1, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h1, h2315, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2109, hlam, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2313, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h3, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2107, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2315, hlam, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2321, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h5, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h5, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2315, h5, h6, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2323, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2107, h2315, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2315, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2106, h2109, hc23, hc45, hlam, hphi, ht34, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                        · linarith only [h2401, hlam, p2325_0]
                      · linarith only [h2400, h4, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2106, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2315, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2317, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h3, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2107, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h1, h2107, h6, hc23, hc45, hlam, hphi, ht34, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2321, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h4, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2108, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h0, h2108, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h0, h2108, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2451 | h2451
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2452 | h2452
          · linarith only [h1, h2452, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2454 | h2454
            · linarith only [h2106, h2108, h2454, h4, h6, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2106, h2108, h2451, h2454, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2457 | h2457
          · linarith only [h1, h2457, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2459 | h2459
            · linarith only [h2106, h2451, h2459, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2461 | h2461
              · linarith only [h0, h2106, h2108, h2461, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2463 | h2463
                · linarith only [h2107, h2108, h2463, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2465 | h2465
                  · linarith only [h2107, h2108, h2459, h2465, h4, h6, hc23, hc34, hlam, hphi]
                  · rcases h2bigk with h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c | h2467c
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      rcases p2467_3 (m.d 0 2) (by simp) with h2469 | h2469
                      · rcases p2467_3 (m.d 1 2) (by simp) with h2470 | h2470
                        · linarith only [h0, h2470, hlam]
                        · rcases p2467_3 (m.d 2 3) (by simp) with h2472 | h2472
                          · linarith only [h2, h2472, hlam]
                          · rcases p2467_3 (m.d 2 4) (by simp) with h2474 | h2474
                            · linarith only [h2474, h3, hlam]
                            · rcases p2467_3 (m.d 2 5) (by simp) with h2476 | h2476
                              · linarith only [h2476, h4, hlam]
                              · linarith only [h2108, h2476, hlam]
                      · linarith only [h0, h2469, hlam]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2107, h2108, h2459, h4, hlam, p2467_2]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2107, h2108, h4, hlam, p2467_2]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2107, h2108, h2459, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h0, hlam, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2108, h2461, hc23, hc35, hlam, hphi, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h0, h2108, h2459, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2108, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2106, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2459, hlam, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2461, hlam, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h3, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2107, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h3, h6, hc23, hc45, hlam, hphi, ht34, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h2463, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h4, hlam, p2467_0]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [h0, h2106, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2467_1]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      rcases p2467_3 (m.d 0 2) (by simp) with h2500 | h2500
                      · rcases p2467_3 (m.d 1 2) (by simp) with h2501 | h2501
                        · linarith only [h2108, h2501, hlam]
                        · linarith only [h2106, h2501, hlam]
                      · linarith only [h2, h2500, hlam]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      rcases p2467_3 (m.d 0 2) (by simp) with h2505 | h2505
                      · rcases p2467_3 (m.d 1 2) (by simp) with h2506 | h2506
                        · linarith only [h2108, h2506, hlam]
                        · linarith only [h2107, h2506, hlam]
                      · linarith only [h2505, h3, hlam]
                    · have p2467_0 := h2467c.1
                      have p2467_1 := h2467c.2.1
                      have p2467_2 := h2467c.2.2.1
                      have p2467_3 := h2467c.2.2.2
                      linarith only [hlam, p2467_0]
    · linarith only [h2106, h2107, h3, h6, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2512 | h2512
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2513 | h2513
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2514 | h2514
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2515 | h2515
          · linarith only [h1, h2515, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2517 | h2517
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2518 | h2518
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2519 | h2519
                · linarith only [h1, h2512, h2519, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2521 | h2521
                  · linarith only [h1, h2512, h2517, h2521, h6, hlam]
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
                      rcases p2523_3 (m.d 0 2) (by simp) with h2525 | h2525
                      · rcases p2523_3 (m.d 1 2) (by simp) with h2526 | h2526
                        · linarith only [h0, h2526, hlam]
                        · rcases p2523_3 (m.d 2 3) (by simp) with h2528 | h2528
                          · linarith only [h2, h2528, hlam]
                          · linarith only [h2106, h2528, hlam]
                      · linarith only [h0, h2525, hlam]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h0, h2106, h2513, hc01, hc25, hlam, hphi, ht0b, ht5b, p2523_1]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2, h2106, h2512, hlam, p2523_2]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2, h2106, h2513, hlam, p2523_2]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h0, hlam, p2523_1]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2106, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2, h2106, h2517, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2523_1]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h0, h2, h2106, hc01, hc25, hlam, hphi, ht0b, ht5b, p2523_1]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h0, h2, h2512, h2517, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2523_1]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      rcases p2523_3 (m.d 0 2) (by simp) with h2543 | h2543
                      · rcases p2523_3 (m.d 1 2) (by simp) with h2544 | h2544
                        · linarith only [h2106, h2544, hlam]
                        · linarith only [h2512, h2544, hlam]
                      · linarith only [h2543, h3, hlam]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      rcases p2523_3 (m.d 0 2) (by simp) with h2548 | h2548
                      · rcases p2523_3 (m.d 1 2) (by simp) with h2549 | h2549
                        · linarith only [h2106, h2549, hlam]
                        · linarith only [h2513, h2549, hlam]
                      · linarith only [h2548, h4, hlam]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h3, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2512, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2517, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2519, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h4, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2513, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h2518, hlam, p2523_0]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [h0, h2513, h2517, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2523_1]
                    · have p2523_0 := h2523c.1
                      have p2523_1 := h2523c.2.1
                      have p2523_2 := h2523c.2.2.1
                      have p2523_3 := h2523c.2.2.2
                      linarith only [hlam, p2523_0]
              · linarith only [h2106, h2513, h2518, hlam]
            · linarith only [h0, h2, h2106, h2513, h2517, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h2106, h2512, h2514, h5, h6, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2566 | h2566
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2567 | h2567
          · linarith only [h1, h2567, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2569 | h2569
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2570 | h2570
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2571 | h2571
                · linarith only [h2512, h2513, h2571, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2573 | h2573
                  · linarith only [h2512, h2513, h2569, h2573, h4, h6, hlam]
                  · rcases h2bigk with h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      rcases p2575_3 (m.d 0 2) (by simp) with h2577 | h2577
                      · rcases p2575_3 (m.d 1 2) (by simp) with h2578 | h2578
                        · linarith only [h0, h2578, hlam]
                        · rcases p2575_3 (m.d 2 3) (by simp) with h2580 | h2580
                          · linarith only [h2, h2580, hlam]
                          · linarith only [h2106, h2580, hlam]
                      · linarith only [h0, h2577, hlam]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h0, h2106, h2512, h2569, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2512, h2513, h4, hlam, p2575_2]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2512, h2513, h2569, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h0, hlam, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2106, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2513, h2569, h4, h6, hc34, hc45, hlam, hphi, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2513, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h0, h2, h2512, h2569, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      rcases p2575_3 (m.d 0 2) (by simp) with h2595 | h2595
                      · rcases p2575_3 (m.d 1 2) (by simp) with h2596 | h2596
                        · linarith only [h2106, h2596, hlam]
                        · linarith only [h2512, h2596, hlam]
                      · linarith only [h2595, h3, hlam]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h0, h2, h2512, h2513, h2569, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h3, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2512, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2569, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2571, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h4, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h0, h2512, h2569, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2575_1]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [h2570, hlam, p2575_0]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      rcases p2575_3 (m.d 0 2) (by simp) with h2609 | h2609
                      · rcases p2575_3 (m.d 1 2) (by simp) with h2610 | h2610
                        · linarith only [h2513, h2610, hlam]
                        · linarith only [h2512, h2610, hlam]
                      · linarith only [h2609, h3, hlam]
                    · have p2575_0 := h2575c.1
                      have p2575_1 := h2575c.2.1
                      have p2575_2 := h2575c.2.2.1
                      have p2575_3 := h2575c.2.2.2
                      linarith only [hlam, p2575_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2615 | h2615
                · linarith only [h1, h2512, h2615, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2617 | h2617
                  · linarith only [h2106, h2512, h2569, h2570, h2617, h4, h6, hlam]
                  · linarith only [h2106, h2512, h2569, h2570, h2617, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2, h2106, h2512, h2569, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h2106, h2512, h2566, h5, h6, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2622 | h2622
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2623 | h2623
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2624 | h2624
          · linarith only [h2512, h2622, h2624, h3, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2512, h2622, h2624, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2627 | h2627
          · linarith only [h2106, h2622, h2623, h2627, h5, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2512, h2622, h2627, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2630 | h2630
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2631 | h2631
          · linarith only [h1, h2631, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2633 | h2633
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2634 | h2634
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2635 | h2635
                · linarith only [h2635, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2637 | h2637
                  · linarith only [h0, h2, h2106, h2630, h2637, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h2bigk with h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      rcases p2639_3 (m.d 0 2) (by simp) with h2641 | h2641
                      · rcases p2639_3 (m.d 1 2) (by simp) with h2642 | h2642
                        · linarith only [h0, h2642, hlam]
                        · rcases p2639_3 (m.d 2 3) (by simp) with h2644 | h2644
                          · linarith only [h2, h2644, hlam]
                          · linarith only [h2106, h2644, hlam]
                      · linarith only [h0, h2641, hlam]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      rcases p2639_3 (m.d 0 2) (by simp) with h2648 | h2648
                      · rcases p2639_3 (m.d 1 2) (by simp) with h2649 | h2649
                        · linarith only [h0, h2649, hlam]
                        · rcases p2639_3 (m.d 2 3) (by simp) with h2651 | h2651
                          · linarith only [h2651, hlam, p2639_0]
                          · rcases p2639_3 (m.d 2 4) (by simp) with h2653 | h2653
                            · linarith only [h2653, h3, hlam]
                            · rcases p2639_3 (m.d 2 5) (by simp) with h2655 | h2655
                              · linarith only [h2655, h4, hlam]
                              · rcases h4bigk with h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h6, hc14, hc45, hlam, hphi, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2512, h6, hc12, hc45, hlam, hphi, ht23, ht34, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h6, hc34, hc45, hlam, hphi, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h6, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h1, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2512, hlam, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2631, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h3, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h0, h2633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2639_1, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2635, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h5, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2630, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2633, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2637, hlam, p2657_0]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2512, hc12, hc45, hlam, hphi, ht23, ht34, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [h2512, hc12, hc45, hlam, hphi, ht23, ht34, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p2657_1]
                                · have p2657_0 := h2657c.1
                                  have p2657_1 := h2657c.2.1
                                  have p2657_2 := h2657c.2.2.1
                                  have p2657_3 := h2657c.2.2.2
                                  linarith only [hlam, p2657_0]
                      · linarith only [h2648, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      rcases p2639_3 (m.d 0 2) (by simp) with h2684 | h2684
                      · rcases p2639_3 (m.d 1 2) (by simp) with h2685 | h2685
                        · linarith only [h0, h2685, hlam]
                        · rcases p2639_3 (m.d 2 3) (by simp) with h2687 | h2687
                          · linarith only [h2, h2687, hlam]
                          · linarith only [h2633, h2687, hlam]
                      · linarith only [h2684, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      rcases p2639_3 (m.d 0 2) (by simp) with h2691 | h2691
                      · rcases p2639_3 (m.d 1 2) (by simp) with h2692 | h2692
                        · linarith only [h0, h2692, hlam]
                        · rcases p2639_3 (m.d 2 3) (by simp) with h2694 | h2694
                          · linarith only [h2, h2694, hlam]
                          · linarith only [h2634, h2694, hlam]
                      · linarith only [h2691, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h0, hlam, p2639_1]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2106, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2512, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2622, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      rcases p2639_3 (m.d 0 2) (by simp) with h2704 | h2704
                      · rcases p2639_3 (m.d 1 2) (by simp) with h2705 | h2705
                        · linarith only [h2705, hlam, p2639_0]
                        · rcases p2639_3 (m.d 2 3) (by simp) with h2707 | h2707
                          · rcases p2639_3 (m.d 2 4) (by simp) with h2708 | h2708
                            · linarith only [h2633, h2708, hlam]
                            · linarith only [h2512, h2708, hlam]
                          · linarith only [h2707, hlam, p2639_0]
                      · linarith only [h0, h2704, hlam]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2512, hc12, hc23, hlam, hphi, p2639_1]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h0, h2, h2512, h2635, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2639_1]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h3, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h3, h6, hc12, hc45, hlam, hphi, ht23, ht34, p2639_1]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2633, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2635, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h4, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      rcases p2639_3 (m.d 0 2) (by simp) with h2722 | h2722
                      · rcases p2639_3 (m.d 1 2) (by simp) with h2723 | h2723
                        · linarith only [h2723, hlam, p2639_0]
                        · rcases p2639_3 (m.d 2 3) (by simp) with h2725 | h2725
                          · rcases p2639_3 (m.d 2 4) (by simp) with h2726 | h2726
                            · linarith only [h2635, h2726, hlam]
                            · linarith only [h2512, h2726, hlam]
                          · linarith only [h2106, h2725, hlam]
                      · linarith only [h0, h2722, hlam]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2634, hlam, p2639_0]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [h2512, hc12, hc25, hlam, hphi, p2639_1]
                    · have p2639_0 := h2639c.1
                      have p2639_1 := h2639c.2.1
                      have p2639_2 := h2639c.2.2.1
                      have p2639_3 := h2639c.2.2.2
                      linarith only [hlam, p2639_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2734 | h2734
                · linarith only [h2734, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2736 | h2736
                  · linarith only [h2512, h2736, h3, h6, hc12, hc34, hlam, hphi, ht23]
                  · rcases h2bigk with h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      rcases p2738_3 (m.d 0 2) (by simp) with h2740 | h2740
                      · rcases p2738_3 (m.d 1 2) (by simp) with h2741 | h2741
                        · linarith only [h0, h2741, hlam]
                        · rcases p2738_3 (m.d 2 3) (by simp) with h2743 | h2743
                          · linarith only [h2, h2743, hlam]
                          · linarith only [h2106, h2743, hlam]
                      · linarith only [h0, h2740, hlam]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      rcases p2738_3 (m.d 0 2) (by simp) with h2747 | h2747
                      · rcases p2738_3 (m.d 1 2) (by simp) with h2748 | h2748
                        · linarith only [h0, h2748, hlam]
                        · rcases p2738_3 (m.d 2 3) (by simp) with h2750 | h2750
                          · linarith only [h2750, hlam, p2738_0]
                          · rcases p2738_3 (m.d 2 4) (by simp) with h2752 | h2752
                            · linarith only [h2752, h3, hlam]
                            · rcases p2738_3 (m.d 2 5) (by simp) with h2754 | h2754
                              · linarith only [h2754, h4, hlam]
                              · linarith only [h2634, h2754, hlam]
                      · linarith only [h2747, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      rcases p2738_3 (m.d 0 2) (by simp) with h2758 | h2758
                      · rcases p2738_3 (m.d 1 2) (by simp) with h2759 | h2759
                        · linarith only [h0, h2759, hlam]
                        · rcases p2738_3 (m.d 2 3) (by simp) with h2761 | h2761
                          · linarith only [h2, h2761, hlam]
                          · linarith only [h2633, h2761, hlam]
                      · linarith only [h2758, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      rcases p2738_3 (m.d 0 2) (by simp) with h2765 | h2765
                      · rcases p2738_3 (m.d 1 2) (by simp) with h2766 | h2766
                        · linarith only [h0, h2766, hlam]
                        · rcases p2738_3 (m.d 2 3) (by simp) with h2768 | h2768
                          · linarith only [h2, h2768, hlam]
                          · rcases p2738_3 (m.d 2 4) (by simp) with h2770 | h2770
                            · linarith only [h2770, h3, hlam]
                            · rcases p2738_3 (m.d 2 5) (by simp) with h2772 | h2772
                              · linarith only [h2772, hlam, p2738_0]
                              · rcases h4bigk with h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2512, h6, hc12, hc45, hlam, hphi, ht23, ht34, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2512, h6, hc12, hc45, hlam, hphi, ht23, ht34, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h6, hc34, hc45, hlam, hphi, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h6, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h1, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2512, hlam, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2631, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h3, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2633, h2634, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p2738_1, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h0, h2633, h2634, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2738_1, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2734, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h5, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2630, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2633, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2736, hlam, p2774_0]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2512, hc12, hc45, hlam, hphi, ht23, ht34, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [h2512, hc12, hc45, hlam, hphi, ht23, ht34, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p2774_1]
                                · have p2774_0 := h2774c.1
                                  have p2774_1 := h2774c.2.1
                                  have p2774_2 := h2774c.2.2.1
                                  have p2774_3 := h2774c.2.2.2
                                  linarith only [hlam, p2774_0]
                      · linarith only [h2765, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h0, hlam, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2106, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2512, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2622, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2634, hc12, hc35, hlam, hphi, ht23, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2512, h2634, hc12, hc35, hlam, hphi, ht23, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2634, hlam, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h3, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h3, h6, hc12, hc45, hlam, hphi, ht23, ht34, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2633, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h2734, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h4, hlam, p2738_0]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      rcases p2738_3 (m.d 0 2) (by simp) with h2817 | h2817
                      · rcases p2738_3 (m.d 1 2) (by simp) with h2818 | h2818
                        · linarith only [h2818, hlam, p2738_0]
                        · rcases p2738_3 (m.d 2 3) (by simp) with h2820 | h2820
                          · linarith only [h2634, h2820, hlam]
                          · linarith only [h2106, h2820, hlam]
                      · linarith only [h0, h2817, hlam]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h0, h2106, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [h0, h2512, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2738_1]
                    · have p2738_0 := h2738c.1
                      have p2738_1 := h2738c.2.1
                      have p2738_2 := h2738c.2.2.1
                      have p2738_3 := h2738c.2.2.2
                      linarith only [hlam, p2738_0]
            · linarith only [h2106, h2633, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2828 | h2828
          · linarith only [h1, h2828, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2830 | h2830
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2831 | h2831
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2832 | h2832
                · linarith only [h2832, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2834 | h2834
                  · linarith only [h2830, h2834, h3, h6, hlam]
                  · rcases h2bigk with h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c | h2836c
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2, h2106, h2630, h2830, hlam, p2836_2]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2106, h2630, h2830, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2836_1]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      rcases p2836_3 (m.d 0 2) (by simp) with h2840 | h2840
                      · rcases p2836_3 (m.d 1 2) (by simp) with h2841 | h2841
                        · linarith only [h0, h2841, hlam]
                        · rcases p2836_3 (m.d 2 3) (by simp) with h2843 | h2843
                          · linarith only [h2, h2843, hlam]
                          · linarith only [h2830, h2843, hlam]
                      · linarith only [h2840, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      rcases p2836_3 (m.d 0 2) (by simp) with h2847 | h2847
                      · rcases p2836_3 (m.d 1 2) (by simp) with h2848 | h2848
                        · linarith only [h0, h2848, hlam]
                        · rcases p2836_3 (m.d 2 3) (by simp) with h2850 | h2850
                          · linarith only [h2, h2850, hlam]
                          · linarith only [h2831, h2850, hlam]
                      · linarith only [h2847, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h0, hlam, p2836_1]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2106, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2512, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2622, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      rcases p2836_3 (m.d 0 2) (by simp) with h2860 | h2860
                      · rcases p2836_3 (m.d 1 2) (by simp) with h2861 | h2861
                        · linarith only [h2861, hlam, p2836_0]
                        · rcases p2836_3 (m.d 2 3) (by simp) with h2863 | h2863
                          · rcases p2836_3 (m.d 2 4) (by simp) with h2864 | h2864
                            · linarith only [h2830, h2864, hlam]
                            · linarith only [h2512, h2864, hlam]
                          · linarith only [h2863, hlam, p2836_0]
                      · linarith only [h0, h2860, hlam]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2106, h2630, h2830, hc12, hc23, hlam, hphi, p2836_1]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h0, h2, h2106, h2630, h2830, h2832, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2836_1]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h3, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h3, h6, hc12, hc45, hlam, hphi, ht23, ht34, p2836_1]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2830, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2832, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h4, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      rcases p2836_3 (m.d 0 2) (by simp) with h2878 | h2878
                      · rcases p2836_3 (m.d 1 2) (by simp) with h2879 | h2879
                        · linarith only [h2879, hlam, p2836_0]
                        · rcases p2836_3 (m.d 2 3) (by simp) with h2881 | h2881
                          · rcases p2836_3 (m.d 2 4) (by simp) with h2882 | h2882
                            · linarith only [h2832, h2882, hlam]
                            · linarith only [h2512, h2882, hlam]
                          · linarith only [h2106, h2881, hlam]
                      · linarith only [h0, h2878, hlam]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2831, hlam, p2836_0]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [h2512, hc12, hc25, hlam, hphi, p2836_1]
                    · have p2836_0 := h2836c.1
                      have p2836_1 := h2836c.2.1
                      have p2836_2 := h2836c.2.2.1
                      have p2836_3 := h2836c.2.2.2
                      linarith only [hlam, p2836_0]
              · linarith only [h2106, h2630, h2830, h2831, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h2106, h2830, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_12_24_L_I_H_I_s5_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6
  · exact r1l7_12_24_L_I_H_I_s5_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6

end R2N4
