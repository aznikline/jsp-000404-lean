import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2082 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2083 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h2084 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2085 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2086 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2087 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2088 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h2089 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 2 3 5 (by decide) (by decide) with h2090 | h2090
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2091 | h2091
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2092 | h2092
      · rcases h0bigk with h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h0, hlam, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h1265, hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h1561, h2083, hlam, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h1561, hlam, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2099 | h2099
          · linarith only [h0, h2099, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2101 | h2101
            · rcases p2093_3 (m.d 0 3) (by simp) with h2102 | h2102
              · linarith only [h2078, h2102, hlam]
              · linarith only [h1265, h2102, hlam]
            · linarith only [h0, h2101, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h0, h2078, h2089, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2108 | h2108
          · linarith only [h0, h2108, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2110 | h2110
            · rcases p2093_3 (m.d 0 3) (by simp) with h2111 | h2111
              · linarith only [h2078, h2111, hlam]
              · linarith only [h2081, h2111, hlam]
            · linarith only [h2079, h2110, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2115 | h2115
          · linarith only [h0, h2115, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2117 | h2117
            · rcases p2093_3 (m.d 0 3) (by simp) with h2118 | h2118
              · linarith only [h2078, h2118, hlam]
              · linarith only [h2082, h2118, hlam]
            · linarith only [h2080, h2117, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2122 | h2122
          · linarith only [h1265, h2122, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2124 | h2124
            · rcases p2093_3 (m.d 0 3) (by simp) with h2125 | h2125
              · rcases p2093_3 (m.d 0 4) (by simp) with h2126 | h2126
                · linarith only [h2081, h2126, hlam]
                · linarith only [h1561, h2083, h2126, hlam]
              · linarith only [h1265, h2125, hlam]
            · linarith only [h0, h2124, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h2078, hlam, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2133 | h2133
          · linarith only [h1265, h2133, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2135 | h2135
            · rcases p2093_3 (m.d 0 3) (by simp) with h2136 | h2136
              · rcases p2093_3 (m.d 0 4) (by simp) with h2137 | h2137
                · linarith only [h2081, h2137, hlam]
                · rcases p2093_3 (m.d 0 5) (by simp) with h2139 | h2139
                  · linarith only [h2082, h2139, hlam]
                  · rcases h3bigk with h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c | h2141c
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h1265, hlam, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h0, h2078, h2089, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h0, h2078, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      rcases p2141_3 (m.d 0 3) (by simp) with h2146 | h2146
                      · rcases p2141_3 (m.d 1 3) (by simp) with h2147 | h2147
                        · rcases p2141_3 (m.d 2 3) (by simp) with h2148 | h2148
                          · linarith only [h2078, h2148, hlam]
                          · linarith only [h2090, h2148, hlam]
                        · linarith only [h2087, h2147, hlam]
                      · linarith only [h2146, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h1561, h2083, hc01, hc13, hlam, hphi, p2093_1, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2084, h2089, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2084, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      rcases p2141_3 (m.d 0 3) (by simp) with h2157 | h2157
                      · linarith only [h1265, h2157, hlam]
                      · linarith only [h2082, h2157, hlam]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2078, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2084, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2092, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h0, h2078, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2081, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2086, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2089, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h1265, h2081, h2084, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2141_1]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2082, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2087, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2090, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [h2092, hlam, p2141_0]
                    · have p2141_0 := h2141c.1
                      have p2141_1 := h2141c.2.1
                      have p2141_2 := h2141c.2.2.1
                      have p2141_3 := h2141c.2.2.2
                      linarith only [hlam, p2141_0]
              · linarith only [h2081, h2136, hlam]
            · linarith only [h2079, h2135, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2177 | h2177
          · linarith only [h1265, h2177, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2179 | h2179
            · rcases p2093_3 (m.d 0 3) (by simp) with h2180 | h2180
              · rcases p2093_3 (m.d 0 4) (by simp) with h2181 | h2181
                · linarith only [h2081, h2181, hlam]
                · linarith only [h2083, h2181, hlam]
              · linarith only [h2082, h2180, hlam]
            · linarith only [h2080, h2179, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2186 | h2186
          · linarith only [h2186, hlam, p2093_0]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2188 | h2188
            · rcases p2093_3 (m.d 0 3) (by simp) with h2189 | h2189
              · rcases p2093_3 (m.d 0 4) (by simp) with h2190 | h2190
                · rcases p2093_3 (m.d 0 5) (by simp) with h2191 | h2191
                  · linarith only [h2083, h2191, hlam]
                  · linarith only [h1561, h2191, hlam]
                · linarith only [h2190, hlam, p2093_0]
              · linarith only [h1265, h2189, hlam]
            · linarith only [h0, h2188, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h2079, hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h2081, hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2200 | h2200
          · linarith only [h1561, h2080, h2088, h2200, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2093_1, u2ehi4]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2202 | h2202
            · rcases p2093_3 (m.d 0 3) (by simp) with h2203 | h2203
              · rcases p2093_3 (m.d 0 4) (by simp) with h2204 | h2204
                · rcases p2093_3 (m.d 0 5) (by simp) with h2205 | h2205
                  · linarith only [h2083, h2205, hlam]
                  · rcases h3bigk with h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h1265, hlam, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h1265, h2084, h2089, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h1265, h2084, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      rcases p2207_3 (m.d 0 3) (by simp) with h2212 | h2212
                      · rcases p2207_3 (m.d 1 3) (by simp) with h2213 | h2213
                        · rcases p2207_3 (m.d 2 3) (by simp) with h2214 | h2214
                          · linarith only [h2078, h2214, hlam]
                          · linarith only [h2090, h2214, hlam]
                        · linarith only [h2087, h2213, hlam]
                      · linarith only [h2212, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2084, h2089, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2084, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      rcases p2207_3 (m.d 0 3) (by simp) with h2223 | h2223
                      · linarith only [h1265, h2223, hlam]
                      · linarith only [h2082, h2223, hlam]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2078, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2084, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2092, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h0, h2078, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2081, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2086, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2089, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h1265, h2081, h2084, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2207_1]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2082, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2087, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2090, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [h2092, hlam, p2207_0]
                    · have p2207_0 := h2207c.1
                      have p2207_1 := h2207c.2.1
                      have p2207_2 := h2207c.2.2.1
                      have p2207_3 := h2207c.2.2.2
                      linarith only [hlam, p2207_0]
                · linarith only [h2083, h2204, hlam]
              · linarith only [h2082, h2203, hlam]
            · linarith only [h2080, h2202, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          rcases p2093_3 (m.d 0 1) (by simp) with h2244 | h2244
          · linarith only [h1561, h2244, hlam]
          · rcases p2093_3 (m.d 0 2) (by simp) with h2246 | h2246
            · rcases p2093_3 (m.d 0 3) (by simp) with h2247 | h2247
              · rcases p2093_3 (m.d 0 4) (by simp) with h2248 | h2248
                · rcases p2093_3 (m.d 0 5) (by simp) with h2249 | h2249
                  · rcases h3bigk with h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c | h2250c
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h1265, hlam, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h1265, h2084, h2089, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h1265, h2084, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      rcases p2250_3 (m.d 0 3) (by simp) with h2255 | h2255
                      · rcases p2250_3 (m.d 1 3) (by simp) with h2256 | h2256
                        · rcases p2250_3 (m.d 2 3) (by simp) with h2257 | h2257
                          · linarith only [h2078, h2257, hlam]
                          · linarith only [h2090, h2257, hlam]
                        · linarith only [h2087, h2256, hlam]
                      · linarith only [h2255, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2084, h2089, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2084, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      rcases p2250_3 (m.d 0 3) (by simp) with h2266 | h2266
                      · linarith only [h1265, h2266, hlam]
                      · linarith only [h2082, h2266, hlam]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2078, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2084, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2092, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h0, h2078, h2092, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2081, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2086, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2089, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2081, h2092, hc03, hc45, hlam, hphi, ht0b, ht5b, p2250_1]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2082, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2087, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2090, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [h2092, hlam, p2250_0]
                    · have p2250_0 := h2250c.1
                      have p2250_1 := h2250c.2.1
                      have p2250_2 := h2250c.2.2.1
                      have p2250_3 := h2250c.2.2.2
                      linarith only [hlam, p2250_0]
                  · linarith only [h1561, h2249, hlam]
                · linarith only [h2083, h2248, hlam, p2093_1]
              · linarith only [h1265, h2247, hlam]
            · linarith only [h0, h2246, hlam]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h2080, hlam, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h2082, hlam, p2093_0]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [h2083, hlam, p2093_1]
        · have p2093_0 := h2093c.1
          have p2093_1 := h2093c.2.1
          have p2093_2 := h2093c.2.2.1
          have p2093_3 := h2093c.2.2.2
          linarith only [hlam, p2093_0]
      · rcases h0bigk with h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h0, hlam, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h1265, hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2079, h2091, h2092, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h1561, hlam, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2298 | h2298
          · linarith only [h0, h2298, hlam]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2300 | h2300
            · rcases p2292_3 (m.d 0 3) (by simp) with h2301 | h2301
              · linarith only [h2078, h2301, hlam]
              · linarith only [h1265, h2301, hlam]
            · linarith only [h0, h2300, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h0, h2078, h2089, h2091, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h0, h2079, h2091, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2308 | h2308
          · linarith only [h0, h2308, hlam]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2310 | h2310
            · rcases p2292_3 (m.d 0 3) (by simp) with h2311 | h2311
              · linarith only [h2078, h2311, hlam]
              · linarith only [h2082, h2311, hlam]
            · linarith only [h2080, h2310, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2315 | h2315
          · linarith only [h1265, h2315, hlam]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2317 | h2317
            · rcases p2292_3 (m.d 0 3) (by simp) with h2318 | h2318
              · rcases p2292_3 (m.d 0 4) (by simp) with h2319 | h2319
                · linarith only [h2081, h2319, hlam]
                · linarith only [h2079, h2091, h2092, h2319, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2292_1]
              · linarith only [h1265, h2318, hlam]
            · linarith only [h0, h2317, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2078, hlam, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h1265, h2079, h2084, h2091, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2327 | h2327
          · linarith only [h1265, h2327, hlam]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2329 | h2329
            · rcases p2292_3 (m.d 0 3) (by simp) with h2330 | h2330
              · rcases p2292_3 (m.d 0 4) (by simp) with h2331 | h2331
                · linarith only [h2081, h2331, hlam]
                · linarith only [h2083, h2331, hlam]
              · linarith only [h2082, h2330, hlam]
            · linarith only [h2080, h2329, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2336 | h2336
          · linarith only [h2336, hlam, p2292_0]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2338 | h2338
            · rcases p2292_3 (m.d 0 3) (by simp) with h2339 | h2339
              · rcases p2292_3 (m.d 0 4) (by simp) with h2340 | h2340
                · rcases p2292_3 (m.d 0 5) (by simp) with h2341 | h2341
                  · linarith only [h2083, h2341, hlam]
                  · linarith only [h1561, h2341, hlam]
                · linarith only [h2340, hlam, p2292_0]
              · linarith only [h1265, h2339, hlam]
            · linarith only [h0, h2338, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2079, hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2081, hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2350 | h2350
          · linarith only [h1561, h2350, hlam, p2292_1]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2352 | h2352
            · rcases p2292_3 (m.d 0 3) (by simp) with h2353 | h2353
              · rcases p2292_3 (m.d 0 4) (by simp) with h2354 | h2354
                · rcases p2292_3 (m.d 0 5) (by simp) with h2355 | h2355
                  · linarith only [h2083, h2355, hlam]
                  · rcases h3bigk with h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h1265, hlam, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h1265, h2084, h2089, h2091, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      rcases p2357_3 (m.d 0 3) (by simp) with h2361 | h2361
                      · rcases p2357_3 (m.d 1 3) (by simp) with h2362 | h2362
                        · rcases p2357_3 (m.d 2 3) (by simp) with h2363 | h2363
                          · linarith only [h2078, h2363, hlam]
                          · linarith only [h2089, h2363, hlam]
                        · linarith only [h2086, h2362, hlam]
                      · linarith only [h2361, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      rcases p2357_3 (m.d 0 3) (by simp) with h2368 | h2368
                      · rcases p2357_3 (m.d 1 3) (by simp) with h2369 | h2369
                        · rcases p2357_3 (m.d 2 3) (by simp) with h2370 | h2370
                          · linarith only [h2078, h2370, hlam]
                          · linarith only [h2090, h2370, hlam]
                        · linarith only [h2087, h2369, hlam]
                      · linarith only [h2368, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2084, h2089, h2091, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      rcases p2357_3 (m.d 0 3) (by simp) with h2378 | h2378
                      · linarith only [h1265, h2378, hlam]
                      · linarith only [h2081, h2378, hlam]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      rcases p2357_3 (m.d 0 3) (by simp) with h2381 | h2381
                      · linarith only [h1265, h2381, hlam]
                      · linarith only [h2082, h2381, hlam]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2078, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2084, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h0, h2078, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2081, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2086, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2089, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2092, hlam, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2082, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2087, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2090, hlam, p2357_0]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [h2082, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2357_1]
                    · have p2357_0 := h2357c.1
                      have p2357_1 := h2357c.2.1
                      have p2357_2 := h2357c.2.2.1
                      have p2357_3 := h2357c.2.2.2
                      linarith only [hlam, p2357_0]
                · linarith only [h2083, h2354, hlam]
              · linarith only [h2082, h2353, hlam]
            · linarith only [h2080, h2352, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          rcases p2292_3 (m.d 0 1) (by simp) with h2402 | h2402
          · linarith only [h1561, h2402, hlam]
          · rcases p2292_3 (m.d 0 2) (by simp) with h2404 | h2404
            · rcases p2292_3 (m.d 0 3) (by simp) with h2405 | h2405
              · rcases p2292_3 (m.d 0 4) (by simp) with h2406 | h2406
                · rcases p2292_3 (m.d 0 5) (by simp) with h2407 | h2407
                  · rcases h3bigk with h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h1265, hlam, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h1265, h2084, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2408_1, u2ehi2]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      rcases p2408_3 (m.d 0 3) (by simp) with h2412 | h2412
                      · rcases p2408_3 (m.d 1 3) (by simp) with h2413 | h2413
                        · rcases p2408_3 (m.d 2 3) (by simp) with h2414 | h2414
                          · linarith only [h2078, h2414, hlam]
                          · linarith only [h2089, h2414, hlam]
                        · linarith only [h2086, h2413, hlam]
                      · linarith only [h2412, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      rcases p2408_3 (m.d 0 3) (by simp) with h2419 | h2419
                      · rcases p2408_3 (m.d 1 3) (by simp) with h2420 | h2420
                        · rcases p2408_3 (m.d 2 3) (by simp) with h2421 | h2421
                          · linarith only [h2078, h2421, hlam]
                          · linarith only [h2090, h2421, hlam]
                        · linarith only [h2087, h2420, hlam]
                      · linarith only [h2419, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2084, h2089, h2091, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      rcases p2408_3 (m.d 0 3) (by simp) with h2429 | h2429
                      · linarith only [h1265, h2429, hlam]
                      · linarith only [h2081, h2429, hlam]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      rcases p2408_3 (m.d 0 3) (by simp) with h2432 | h2432
                      · linarith only [h1265, h2432, hlam]
                      · linarith only [h2082, h2432, hlam]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2078, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2084, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h0, h2078, h2092, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2081, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2086, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2089, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2092, hlam, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2082, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2087, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2090, hlam, p2408_0]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [h2082, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2408_1]
                    · have p2408_0 := h2408c.1
                      have p2408_1 := h2408c.2.1
                      have p2408_2 := h2408c.2.2.1
                      have p2408_3 := h2408c.2.2.2
                      linarith only [hlam, p2408_0]
                  · linarith only [h1561, h2407, hlam]
                · linarith only [h2083, h2406, hlam, p2292_1]
              · linarith only [h1265, h2405, hlam]
            · linarith only [h0, h2404, hlam]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2080, hlam, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2082, hlam, p2292_0]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [h2083, hlam, p2292_1]
        · have p2292_0 := h2292c.1
          have p2292_1 := h2292c.2.1
          have p2292_2 := h2292c.2.2.1
          have p2292_3 := h2292c.2.2.2
          linarith only [hlam, p2292_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2458 | h2458
      · linarith only [h2091, h2458, hc34, hlam, hphi, ht23, u2ehi3]
      · rcases h0bigk with h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c | h2460c
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h0, hlam, p2460_1]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h1265, hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2083, h2091, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h1561, hlam, p2460_1]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          rcases p2460_3 (m.d 0 1) (by simp) with h2466 | h2466
          · linarith only [h0, h2466, hlam]
          · rcases p2460_3 (m.d 0 2) (by simp) with h2468 | h2468
            · rcases p2460_3 (m.d 0 3) (by simp) with h2469 | h2469
              · linarith only [h2078, h2469, hlam]
              · linarith only [h1265, h2469, hlam]
            · linarith only [h0, h2468, hlam]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h0, h2081, h2083, h2091, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h0, h2083, h2091, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h0, h2083, h2091, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          rcases p2460_3 (m.d 0 1) (by simp) with h2477 | h2477
          · linarith only [h1265, h2477, hlam]
          · rcases p2460_3 (m.d 0 2) (by simp) with h2479 | h2479
            · rcases p2460_3 (m.d 0 3) (by simp) with h2480 | h2480
              · rcases p2460_3 (m.d 0 4) (by simp) with h2481 | h2481
                · linarith only [h2081, h2481, hlam]
                · linarith only [h2083, h2091, h2481, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
              · linarith only [h1265, h2480, hlam]
            · linarith only [h0, h2479, hlam]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2078, hlam, p2460_1]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2083, h2091, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h0, h2078, h2083, h2091, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          rcases p2460_3 (m.d 0 1) (by simp) with h2490 | h2490
          · linarith only [h2490, hlam, p2460_0]
          · rcases p2460_3 (m.d 0 2) (by simp) with h2492 | h2492
            · rcases p2460_3 (m.d 0 3) (by simp) with h2493 | h2493
              · rcases p2460_3 (m.d 0 4) (by simp) with h2494 | h2494
                · rcases p2460_3 (m.d 0 5) (by simp) with h2495 | h2495
                  · linarith only [h2083, h2495, hlam]
                  · linarith only [h1561, h2495, hlam]
                · linarith only [h2494, hlam, p2460_0]
              · linarith only [h1265, h2493, hlam]
            · linarith only [h0, h2492, hlam]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2079, hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2081, hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2083, h2091, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          rcases p2460_3 (m.d 0 1) (by simp) with h2505 | h2505
          · linarith only [h1561, h2505, hlam]
          · rcases p2460_3 (m.d 0 2) (by simp) with h2507 | h2507
            · rcases p2460_3 (m.d 0 3) (by simp) with h2508 | h2508
              · rcases p2460_3 (m.d 0 4) (by simp) with h2509 | h2509
                · rcases p2460_3 (m.d 0 5) (by simp) with h2510 | h2510
                  · rcases h3bigk with h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h1265, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2078, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2511_1, u2ehi2]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 3) (by simp) with h2515 | h2515
                      · rcases p2511_3 (m.d 1 3) (by simp) with h2516 | h2516
                        · rcases p2511_3 (m.d 2 3) (by simp) with h2517 | h2517
                          · linarith only [h2078, h2517, hlam]
                          · linarith only [h2089, h2517, hlam]
                        · linarith only [h2086, h2516, hlam]
                      · linarith only [h2515, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 3) (by simp) with h2522 | h2522
                      · rcases p2511_3 (m.d 1 3) (by simp) with h2523 | h2523
                        · rcases p2511_3 (m.d 2 3) (by simp) with h2524 | h2524
                          · linarith only [h2078, h2524, hlam]
                          · linarith only [h2090, h2524, hlam]
                        · linarith only [h2087, h2523, hlam]
                      · linarith only [h2522, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2084, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2511_1, u2ehi2]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 3) (by simp) with h2532 | h2532
                      · linarith only [h1265, h2532, hlam]
                      · linarith only [h2081, h2532, hlam]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 3) (by simp) with h2535 | h2535
                      · linarith only [h1265, h2535, hlam]
                      · linarith only [h2082, h2535, hlam]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2078, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2084, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2078, h2458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2081, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2086, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2089, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2458, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2082, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2087, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2090, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2082, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                  · linarith only [h1561, h2510, hlam]
                · linarith only [h2083, h2091, h2509, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2460_1, u2ehi3]
              · linarith only [h1265, h2508, hlam]
            · linarith only [h0, h2507, hlam]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2080, hlam, p2460_1]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2082, hlam, p2460_0]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [h2083, hlam, p2460_1]
        · have p2460_0 := h2460c.1
          have p2460_1 := h2460c.2.1
          have p2460_2 := h2460c.2.2.1
          have p2460_3 := h2460c.2.2.2
          linarith only [hlam, p2460_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2561 | h2561
    · linarith only [h2089, h2090, h2561, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2563 | h2563
      · linarith only [h2561, h2563, hc34, hlam, hphi, ht23, u2ehi3]
      · rcases h0bigk with h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h0, hlam, p2565_1]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h1265, hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h1561, h2083, hlam, p2565_1]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h1561, hlam, p2565_1]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          rcases p2565_3 (m.d 0 1) (by simp) with h2571 | h2571
          · linarith only [h0, h2571, hlam]
          · rcases p2565_3 (m.d 0 2) (by simp) with h2573 | h2573
            · rcases p2565_3 (m.d 0 3) (by simp) with h2574 | h2574
              · linarith only [h2078, h2574, hlam]
              · linarith only [h1265, h2574, hlam]
            · linarith only [h0, h2573, hlam]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h0, h2081, h2083, h2089, h2090, h2563, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2565_1, u2ehi3]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h0, h2083, h2089, h2090, h2563, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2565_1, u2ehi3]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h0, h2083, h2089, h2090, h2563, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2565_1, u2ehi3]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          rcases p2565_3 (m.d 0 1) (by simp) with h2582 | h2582
          · linarith only [h1265, h2582, hlam]
          · rcases p2565_3 (m.d 0 2) (by simp) with h2584 | h2584
            · rcases p2565_3 (m.d 0 3) (by simp) with h2585 | h2585
              · rcases p2565_3 (m.d 0 4) (by simp) with h2586 | h2586
                · linarith only [h2081, h2586, hlam]
                · linarith only [h0, h2083, h2089, h2090, h2563, h2586, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h1265, h2585, hlam]
            · linarith only [h0, h2584, hlam]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2078, hlam, p2565_1]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2083, h2089, h2090, h2563, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2565_1, u2ehi3]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h1265, h2083, h2084, h2089, h2090, h2563, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2565_1, u2ehi3]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          rcases p2565_3 (m.d 0 1) (by simp) with h2595 | h2595
          · linarith only [h2595, hlam, p2565_0]
          · rcases p2565_3 (m.d 0 2) (by simp) with h2597 | h2597
            · rcases p2565_3 (m.d 0 3) (by simp) with h2598 | h2598
              · rcases p2565_3 (m.d 0 4) (by simp) with h2599 | h2599
                · rcases p2565_3 (m.d 0 5) (by simp) with h2600 | h2600
                  · linarith only [h2083, h2600, hlam]
                  · linarith only [h1561, h2600, hlam]
                · linarith only [h2599, hlam, p2565_0]
              · linarith only [h1265, h2598, hlam]
            · linarith only [h0, h2597, hlam]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2079, hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2081, hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2083, h2089, h2090, h2563, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2565_1, u2ehi3]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          rcases p2565_3 (m.d 0 1) (by simp) with h2610 | h2610
          · linarith only [h1561, h2610, hlam]
          · rcases p2565_3 (m.d 0 2) (by simp) with h2612 | h2612
            · rcases p2565_3 (m.d 0 3) (by simp) with h2613 | h2613
              · rcases p2565_3 (m.d 0 4) (by simp) with h2614 | h2614
                · rcases p2565_3 (m.d 0 5) (by simp) with h2615 | h2615
                  · rcases h3bigk with h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c | h2616c
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h1265, hlam, p2616_1]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h1265, h2084, h2089, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2616_1, u2ehi3]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      rcases p2616_3 (m.d 0 3) (by simp) with h2620 | h2620
                      · rcases p2616_3 (m.d 1 3) (by simp) with h2621 | h2621
                        · rcases p2616_3 (m.d 2 3) (by simp) with h2622 | h2622
                          · linarith only [h2078, h2622, hlam]
                          · linarith only [h2089, h2622, hlam]
                        · linarith only [h2086, h2621, hlam]
                      · linarith only [h2620, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h1265, h2084, h2089, h2090, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2616_1, u2ehi3]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h1265, h2084, hc01, hc12, hlam, hphi, p2616_1]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2084, h2089, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2616_1, u2ehi3]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      rcases p2616_3 (m.d 0 3) (by simp) with h2631 | h2631
                      · linarith only [h1265, h2631, hlam]
                      · linarith only [h2081, h2631, hlam]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2084, h2089, h2090, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2616_1, u2ehi3]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2078, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2084, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2081, h2083, h2090, h2563, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2616_1]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2090, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2081, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2086, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2089, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2563, hlam, p2616_1]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2082, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2087, hlam, p2616_0]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h2081, h2083, h2563, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2616_1]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [h1265, h2081, h2083, h2084, h2563, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2616_1]
                    · have p2616_0 := h2616c.1
                      have p2616_1 := h2616c.2.1
                      have p2616_2 := h2616c.2.2.1
                      have p2616_3 := h2616c.2.2.2
                      linarith only [hlam, p2616_0]
                  · linarith only [h1561, h2615, hlam]
                · linarith only [h2083, h2614, hlam, p2565_1]
              · linarith only [h1265, h2613, hlam]
            · linarith only [h0, h2612, hlam]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2080, hlam, p2565_1]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2082, hlam, p2565_0]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [h2083, hlam, p2565_1]
        · have p2565_0 := h2565c.1
          have p2565_1 := h2565c.2.1
          have p2565_2 := h2565c.2.2.1
          have p2565_3 := h2565c.2.2.2
          linarith only [hlam, p2565_0]

end R2N4
