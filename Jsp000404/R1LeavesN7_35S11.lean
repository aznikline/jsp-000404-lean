import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2134 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2135 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2136 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2137 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2138 | h2138
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2139 | h2139
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2140 | h2140
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2141 | h2141
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2142 | h2142
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2143 | h2143
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2144 | h2144
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2145 | h2145
                · rcases h2bigk with h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h0, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2143, h2145, hc02, hlam, hphi, ht0b, ht5b, p2146_1, u5ehi4]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h0, h2145, hc12, hlam, hphi, ht01, ht0b, ht5b, p2146_1, u5ehi4]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h0, h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2146_1, u5ehi3]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2146_1]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2143, h2145, hc12, hlam, hphi, ht01, ht0b, ht5b, p2146_1, u5ehi4]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2145, hc12, hlam, hphi, ht01, ht0b, ht5b, p2146_1, u5ehi4]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2146_1, u5ehi3]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2134, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2139, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2134, h2145, hc02, hlam, hphi, ht0b, ht5b, p2146_1, u5ehi4]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h0, h2134, h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2146_1, u5ehi3]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2135, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2140, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2143, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2135, h2144, hc04, hlam, hphi, ht0b, ht5b, p2146_1, u5ehi3]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2136, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2141, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2144, hlam, p2146_0]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [h2145, hlam, p2146_1]
                  · have p2146_0 := h2146c.1
                    have p2146_1 := h2146c.2.1
                    have p2146_2 := h2146c.2.2.1
                    have p2146_3 := h2146c.2.2.2
                    linarith only [hlam, p2146_0]
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
                    linarith only [h0, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h0, h2143, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    rcases p2172_3 (m.d 0 2) (by simp) with h2176 | h2176
                    · rcases p2172_3 (m.d 1 2) (by simp) with h2177 | h2177
                      · rcases p2172_3 (m.d 2 3) (by simp) with h2178 | h2178
                        · linarith only [h2134, h2178, hlam]
                        · linarith only [h2143, h2178, hlam]
                      · linarith only [h2140, h2177, hlam]
                    · linarith only [h2176, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h0, h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2172_1, u5ehi3]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2134, h2137, h2138, hc12, hlam, hphi, ht01, ht0b, ht5b, p2172_1, u5ehi0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2172_1, u5ehi3]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    rcases p2172_3 (m.d 0 2) (by simp) with h2187 | h2187
                    · linarith only [h0, h2187, hlam]
                    · linarith only [h2135, h2187, hlam]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2172_1, u5ehi3]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2134, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2139, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2134, h2143, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2172_1]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h0, h2134, h2144, hc12, hlam, hphi, ht01, ht0b, ht5b, p2172_1, u5ehi3]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2135, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2140, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2143, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2145, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2136, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2141, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h2144, hlam, p2172_0]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [h0, h2136, h2143, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                  · have p2172_0 := h2172c.1
                    have p2172_1 := h2172c.2.1
                    have p2172_2 := h2172c.2.2.1
                    have p2172_3 := h2172c.2.2.2
                    linarith only [hlam, p2172_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2206 | h2206
                · linarith only [h2143, h2144, h2206, hlam]
                · rcases h2bigk with h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, h2143, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    rcases p2208_3 (m.d 0 2) (by simp) with h2212 | h2212
                    · rcases p2208_3 (m.d 1 2) (by simp) with h2213 | h2213
                      · rcases p2208_3 (m.d 2 3) (by simp) with h2214 | h2214
                        · linarith only [h2134, h2214, hlam]
                        · linarith only [h2143, h2214, hlam]
                      · linarith only [h2140, h2213, hlam]
                    · linarith only [h2212, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, h2143, h2144, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2134, h2137, h2138, hc12, hlam, hphi, ht01, ht0b, ht5b, p2208_1, u5ehi4]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2143, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    rcases p2208_3 (m.d 0 2) (by simp) with h2223 | h2223
                    · linarith only [h0, h2223, hlam]
                    · linarith only [h2135, h2223, hlam]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2143, h2144, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2134, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2139, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2134, h2137, h2138, h2143, h2144, h2206, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2144, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2135, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2140, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2143, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2206, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2136, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2141, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2134, h2137, h2138, h2206, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, h2134, h2137, h2138, h2143, h2206, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2242 | h2242
              · linarith only [h2142, h2143, h2242, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2244 | h2244
                · rcases h2bigk with h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h0, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    rcases p2245_3 (m.d 0 2) (by simp) with h2248 | h2248
                    · rcases p2245_3 (m.d 1 2) (by simp) with h2249 | h2249
                      · rcases p2245_3 (m.d 2 3) (by simp) with h2250 | h2250
                        · linarith only [h2250, hlam, p2245_0]
                        · rcases p2245_3 (m.d 2 4) (by simp) with h2252 | h2252
                          · linarith only [h2135, h2252, hlam]
                          · linarith only [h2143, h2252, hlam]
                      · linarith only [h2139, h2249, hlam]
                    · linarith only [h2248, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h0, h2244, hc12, hlam, hphi, ht01, ht0b, ht5b, p2245_1, u5ehi4]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2245_1, u5ehi2]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2134, h2137, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2245_1]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    rcases p2245_3 (m.d 0 2) (by simp) with h2261 | h2261
                    · linarith only [h0, h2261, hlam]
                    · linarith only [h2134, h2261, hlam]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2244, hc12, hlam, hphi, ht01, ht0b, ht5b, p2245_1, u5ehi4]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2244, hc12, hlam, hphi, ht01, ht0b, ht5b, p2245_1, u5ehi4]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2134, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2139, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2143, hlam, p2245_1]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2242, hlam, p2245_1]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2135, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2140, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2134, h2137, h2143, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2245_1]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h0, h2134, h2137, h2143, h2244, hc12, hlam, hphi, ht01, ht0b, ht5b, p2245_1, u5ehi4]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2136, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2141, hlam, p2245_0]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2245_1]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [h2244, hlam, p2245_1]
                  · have p2245_0 := h2245c.1
                    have p2245_1 := h2245c.2.1
                    have p2245_2 := h2245c.2.2.1
                    have p2245_3 := h2245c.2.2.2
                    linarith only [hlam, p2245_0]
                · rcases h2bigk with h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c | h2281c
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h0, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    rcases p2281_3 (m.d 0 2) (by simp) with h2284 | h2284
                    · rcases p2281_3 (m.d 1 2) (by simp) with h2285 | h2285
                      · rcases p2281_3 (m.d 2 3) (by simp) with h2286 | h2286
                        · linarith only [h2286, hlam, p2281_0]
                        · rcases p2281_3 (m.d 2 4) (by simp) with h2288 | h2288
                          · linarith only [h2135, h2288, hlam]
                          · linarith only [h2143, h2288, hlam]
                      · linarith only [h2139, h2285, hlam]
                    · linarith only [h2284, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    rcases p2281_3 (m.d 0 2) (by simp) with h2293 | h2293
                    · rcases p2281_3 (m.d 1 2) (by simp) with h2294 | h2294
                      · rcases p2281_3 (m.d 2 3) (by simp) with h2295 | h2295
                        · linarith only [h2134, h2295, hlam]
                        · rcases p2281_3 (m.d 2 4) (by simp) with h2297 | h2297
                          · linarith only [h2297, hlam, p2281_0]
                          · rcases p2281_3 (m.d 2 5) (by simp) with h2299 | h2299
                            · linarith only [h2136, h2299, hlam]
                            · linarith only [h2244, h2299, hlam]
                      · linarith only [h2140, h2294, hlam]
                    · linarith only [h2293, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2281_1, u5ehi2]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2134, h2137, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2281_1]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    rcases p2281_3 (m.d 0 2) (by simp) with h2307 | h2307
                    · linarith only [h0, h2307, hlam]
                    · linarith only [h2134, h2307, hlam]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    rcases p2281_3 (m.d 0 2) (by simp) with h2310 | h2310
                    · linarith only [h0, h2310, hlam]
                    · linarith only [h2135, h2310, hlam]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2281_1, u5ehi2]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2134, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2139, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2143, hlam, p2281_1]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2242, hlam, p2281_1]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2135, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2140, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2134, h2137, h2138, h2244, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2281_1]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2244, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2136, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h2141, hlam, p2281_0]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2281_1]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [h0, h2134, h2137, h2138, h2244, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2281_1]
                  · have p2281_0 := h2281c.1
                    have p2281_1 := h2281c.2.1
                    have p2281_2 := h2281c.2.2.1
                    have p2281_3 := h2281c.2.2.2
                    linarith only [hlam, p2281_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2329 | h2329
            · linarith only [h2139, h2142, h2329, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2331 | h2331
              · linarith only [h0, h2134, h2137, h2139, h2142, h2331, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2333 | h2333
                · rcases h2bigk with h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h0, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    rcases p2334_3 (m.d 0 2) (by simp) with h2337 | h2337
                    · rcases p2334_3 (m.d 1 2) (by simp) with h2338 | h2338
                      · rcases p2334_3 (m.d 2 3) (by simp) with h2339 | h2339
                        · linarith only [h2339, hlam, p2334_0]
                        · rcases p2334_3 (m.d 2 4) (by simp) with h2341 | h2341
                          · linarith only [h2135, h2341, hlam]
                          · linarith only [h2329, h2341, hlam]
                      · linarith only [h2139, h2338, hlam]
                    · linarith only [h2337, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h0, h2333, hc12, hlam, hphi, ht01, ht0b, ht5b, p2334_1, u5ehi2]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2334_1, u5ehi2]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2134, h2137, h2142, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2334_1]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    rcases p2334_3 (m.d 0 2) (by simp) with h2350 | h2350
                    · linarith only [h0, h2350, hlam]
                    · linarith only [h2134, h2350, hlam]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2333, hc12, hlam, hphi, ht01, ht0b, ht5b, p2334_1, u5ehi4]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2333, hc12, hlam, hphi, ht01, ht0b, ht5b, p2334_1, u5ehi4]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2134, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2139, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2329, hlam, p2334_1]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2331, hlam, p2334_1]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2135, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2140, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2134, h2137, h2140, h2142, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2334_1]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h0, h2134, h2137, h2140, h2142, h2333, hc12, hlam, hphi, ht01, ht0b, ht5b, p2334_1, u5ehi4]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2136, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2141, hlam, p2334_0]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2334_1]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [h2333, hlam, p2334_1]
                  · have p2334_0 := h2334c.1
                    have p2334_1 := h2334c.2.1
                    have p2334_2 := h2334c.2.2.1
                    have p2334_3 := h2334c.2.2.2
                    linarith only [hlam, p2334_0]
                · rcases h2bigk with h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h0, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    rcases p2370_3 (m.d 0 2) (by simp) with h2373 | h2373
                    · rcases p2370_3 (m.d 1 2) (by simp) with h2374 | h2374
                      · rcases p2370_3 (m.d 2 3) (by simp) with h2375 | h2375
                        · linarith only [h2375, hlam, p2370_0]
                        · rcases p2370_3 (m.d 2 4) (by simp) with h2377 | h2377
                          · linarith only [h2135, h2377, hlam]
                          · linarith only [h2329, h2377, hlam]
                      · linarith only [h2139, h2374, hlam]
                    · linarith only [h2373, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    rcases p2370_3 (m.d 0 2) (by simp) with h2382 | h2382
                    · rcases p2370_3 (m.d 1 2) (by simp) with h2383 | h2383
                      · rcases p2370_3 (m.d 2 3) (by simp) with h2384 | h2384
                        · linarith only [h2134, h2384, hlam]
                        · rcases p2370_3 (m.d 2 4) (by simp) with h2386 | h2386
                          · linarith only [h2386, hlam, p2370_0]
                          · rcases p2370_3 (m.d 2 5) (by simp) with h2388 | h2388
                            · linarith only [h2136, h2388, hlam]
                            · linarith only [h2333, h2388, hlam]
                      · linarith only [h2140, h2383, hlam]
                    · linarith only [h2382, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2370_1, u5ehi2]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2134, h2137, h2142, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2370_1]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    rcases p2370_3 (m.d 0 2) (by simp) with h2396 | h2396
                    · linarith only [h0, h2396, hlam]
                    · linarith only [h2134, h2396, hlam]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    rcases p2370_3 (m.d 0 2) (by simp) with h2399 | h2399
                    · linarith only [h0, h2399, hlam]
                    · linarith only [h2135, h2399, hlam]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2370_1, u5ehi2]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2134, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2139, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2329, hlam, p2370_1]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2331, hlam, p2370_1]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2135, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2140, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2134, h2137, h2138, h2333, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2370_1]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2333, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2136, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h2141, hlam, p2370_0]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2370_1]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [h0, h2134, h2137, h2138, h2333, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2370_1]
                  · have p2370_0 := h2370c.1
                    have p2370_1 := h2370c.2.1
                    have p2370_2 := h2370c.2.2.1
                    have p2370_3 := h2370c.2.2.2
                    linarith only [hlam, p2370_0]
        · linarith only [h0, h2136, h2141, hlam]
      · linarith only [h0, h2135, h2140, hlam]
    · linarith only [h0, h2134, h2139, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2421 | h2421
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2422 | h2422
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2423 | h2423
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2424 | h2424
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2425 | h2425
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2426 | h2426
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2427 | h2427
                · linarith only [h2135, h2138, h2427, hlam]
                · rcases h2bigk with h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h0, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2426, hc02, hlam, hphi, ht0b, ht5b, p2429_1, u5ehi3]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    rcases p2429_3 (m.d 0 2) (by simp) with h2433 | h2433
                    · rcases p2429_3 (m.d 1 2) (by simp) with h2434 | h2434
                      · rcases p2429_3 (m.d 2 3) (by simp) with h2435 | h2435
                        · linarith only [h2134, h2435, hlam]
                        · linarith only [h2425, h2435, hlam]
                      · linarith only [h2422, h2434, hlam]
                    · linarith only [h2433, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2429_1, u5ehi2]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2429_1]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2426, hc12, hlam, hphi, ht01, ht0b, ht5b, p2429_1, u5ehi3]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    rcases p2429_3 (m.d 0 2) (by simp) with h2444 | h2444
                    · linarith only [h0, h2444, hlam]
                    · linarith only [h2135, h2444, hlam]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2426, hc12, hlam, hphi, ht01, ht0b, ht5b, p2429_1, u5ehi3]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2134, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2421, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2134, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2429_1]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h0, h2134, h2426, hc12, hlam, hphi, ht01, ht0b, ht5b, p2429_1, u5ehi3]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2135, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2422, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2425, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2427, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2136, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2423, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h2426, hlam, p2429_0]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [h0, h2136, h2425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2429_1]
                  · have p2429_0 := h2429c.1
                    have p2429_1 := h2429c.2.1
                    have p2429_2 := h2429c.2.2.1
                    have p2429_3 := h2429c.2.2.2
                    linarith only [hlam, p2429_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2463 | h2463
                · linarith only [h2135, h2138, h2463, hlam]
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
                    linarith only [h0, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h0, h2425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    rcases p2465_3 (m.d 0 2) (by simp) with h2469 | h2469
                    · rcases p2465_3 (m.d 1 2) (by simp) with h2470 | h2470
                      · rcases p2465_3 (m.d 2 3) (by simp) with h2471 | h2471
                        · linarith only [h2134, h2471, hlam]
                        · linarith only [h2425, h2471, hlam]
                      · linarith only [h2422, h2470, hlam]
                    · linarith only [h2469, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2465_1, u5ehi2]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    rcases p2465_3 (m.d 0 2) (by simp) with h2480 | h2480
                    · linarith only [h0, h2480, hlam]
                    · linarith only [h2135, h2480, hlam]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2425, h2426, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2134, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2421, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2136, h2425, h2426, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2426, hlam, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2135, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2422, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2425, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2463, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2136, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2423, hlam, p2465_0]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h2136, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [h0, h2136, h2425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2465_1]
                  · have p2465_0 := h2465c.1
                    have p2465_1 := h2465c.2.1
                    have p2465_2 := h2465c.2.2.1
                    have p2465_3 := h2465c.2.2.2
                    linarith only [hlam, p2465_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2499 | h2499
              · linarith only [h2137, h2138, h2425, h2499, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2501 | h2501
                · linarith only [h0, h2135, h2137, h2138, h2425, h2501, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases h2bigk with h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h0, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    rcases p2503_3 (m.d 0 2) (by simp) with h2506 | h2506
                    · rcases p2503_3 (m.d 1 2) (by simp) with h2507 | h2507
                      · rcases p2503_3 (m.d 2 3) (by simp) with h2508 | h2508
                        · linarith only [h2508, hlam, p2503_0]
                        · rcases p2503_3 (m.d 2 4) (by simp) with h2510 | h2510
                          · linarith only [h2135, h2510, hlam]
                          · linarith only [h2425, h2510, hlam]
                      · linarith only [h2421, h2507, hlam]
                    · linarith only [h2506, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    rcases p2503_3 (m.d 0 2) (by simp) with h2515 | h2515
                    · rcases p2503_3 (m.d 1 2) (by simp) with h2516 | h2516
                      · rcases p2503_3 (m.d 2 3) (by simp) with h2517 | h2517
                        · linarith only [h2134, h2517, hlam]
                        · rcases p2503_3 (m.d 2 4) (by simp) with h2519 | h2519
                          · linarith only [h2519, hlam, p2503_0]
                          · rcases p2503_3 (m.d 2 5) (by simp) with h2521 | h2521
                            · linarith only [h2136, h2521, hlam]
                            · linarith only [h2501, h2521, hlam]
                      · linarith only [h2422, h2516, hlam]
                    · linarith only [h2515, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2503_1, u5ehi2]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2503_1]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    rcases p2503_3 (m.d 0 2) (by simp) with h2529 | h2529
                    · linarith only [h0, h2529, hlam]
                    · linarith only [h2134, h2529, hlam]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    rcases p2503_3 (m.d 0 2) (by simp) with h2532 | h2532
                    · linarith only [h0, h2532, hlam]
                    · linarith only [h2135, h2532, hlam]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2503_1, u5ehi2]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2134, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2421, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2425, hlam, p2503_1]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2499, hlam, p2503_1]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2135, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2422, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2503_1]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2501, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2136, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h2423, hlam, p2503_0]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2503_1]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [h0, h2136, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2503_1]
                  · have p2503_0 := h2503c.1
                    have p2503_1 := h2503c.2.1
                    have p2503_2 := h2503c.2.2.1
                    have p2503_3 := h2503c.2.2.2
                    linarith only [hlam, p2503_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2551 | h2551
            · linarith only [h2421, h2424, h2551, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2553 | h2553
              · linarith only [h2137, h2421, h2424, h2553, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2555 | h2555
                · linarith only [h0, h2135, h2137, h2138, h2424, h2555, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases h2bigk with h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c | h2557c
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h0, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    rcases p2557_3 (m.d 0 2) (by simp) with h2560 | h2560
                    · rcases p2557_3 (m.d 1 2) (by simp) with h2561 | h2561
                      · rcases p2557_3 (m.d 2 3) (by simp) with h2562 | h2562
                        · linarith only [h2562, hlam, p2557_0]
                        · rcases p2557_3 (m.d 2 4) (by simp) with h2564 | h2564
                          · linarith only [h2135, h2564, hlam]
                          · linarith only [h2551, h2564, hlam]
                      · linarith only [h2421, h2561, hlam]
                    · linarith only [h2560, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    rcases p2557_3 (m.d 0 2) (by simp) with h2569 | h2569
                    · rcases p2557_3 (m.d 1 2) (by simp) with h2570 | h2570
                      · rcases p2557_3 (m.d 2 3) (by simp) with h2571 | h2571
                        · linarith only [h2134, h2571, hlam]
                        · rcases p2557_3 (m.d 2 4) (by simp) with h2573 | h2573
                          · linarith only [h2573, hlam, p2557_0]
                          · rcases p2557_3 (m.d 2 5) (by simp) with h2575 | h2575
                            · linarith only [h2136, h2575, hlam]
                            · linarith only [h2555, h2575, hlam]
                      · linarith only [h2422, h2570, hlam]
                    · linarith only [h2569, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2557_1, u5ehi2]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p2557_1]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    rcases p2557_3 (m.d 0 2) (by simp) with h2583 | h2583
                    · linarith only [h0, h2583, hlam]
                    · linarith only [h2134, h2583, hlam]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    rcases p2557_3 (m.d 0 2) (by simp) with h2586 | h2586
                    · linarith only [h0, h2586, hlam]
                    · linarith only [h2135, h2586, hlam]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2557_1, u5ehi2]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2134, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2421, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2551, hlam, p2557_1]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2553, hlam, p2557_1]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2135, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2422, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2135, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2557_1]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2555, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2136, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h2423, hlam, p2557_0]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h0, h2136, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2557_1]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [h0, h2136, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2557_1]
                  · have p2557_0 := h2557c.1
                    have p2557_1 := h2557c.2.1
                    have p2557_2 := h2557c.2.2.1
                    have p2557_3 := h2557c.2.2.2
                    linarith only [hlam, p2557_0]
        · linarith only [h0, h2136, h2423, hlam]
      · linarith only [h0, h2135, h2422, hlam]
    · linarith only [h0, h2134, h2421, hlam]

end R2N4
