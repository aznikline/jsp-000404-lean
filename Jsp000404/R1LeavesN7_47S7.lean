import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_47S5
import Jsp000404.R1LeavesN7_47S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1452 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1752 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2140 | h2140
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2141 | h2141
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2142 | h2142
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2143 | h2143
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2144 | h2144
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2145 | h2145
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2146 | h2146
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2147 | h2147
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2148 | h2148
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2149 | h2149
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2151 | h2151
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2152 | h2152
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2153 | h2153
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2154 | h2154
                              · rcases h0bigk with h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h0, hlam, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h1452, hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h1752, hlam, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h1752, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2155_1, u4elo1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h0, h2141, h2151, h2154, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h0, h1752, h2140, h2149, h2152, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  rcases p2155_3 (m.d 0 1) (by simp) with h2165 | h2165
                                  · linarith only [h0, h2165, hlam]
                                  · linarith only [h2140, h2165, hlam]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2140, h2149, h2152, h2154, hc03, hc45, hlam, hphi, ht0b, ht5b, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2141, hlam, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h0, h1752, h2140, h2141, h2149, h2152, h2154, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  rcases p2155_3 (m.d 0 1) (by simp) with h2172 | h2172
                                  · linarith only [h1452, h2172, hlam]
                                  · linarith only [h2140, h2172, hlam]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2140, h2149, h2152, h2154, hc04, hc45, hlam, hphi, ht0b, ht5b, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2142, hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2144, hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h1752, h2140, h2149, h2152, h2154, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2155_1, u4elo1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2140, hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2143, hlam, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2145, hlam, p2155_0]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [h2146, hlam, p2155_1]
                                · have p2155_0 := h2155c.1
                                  have p2155_1 := h2155c.2.1
                                  have p2155_2 := h2155c.2.2.1
                                  have p2155_3 := h2155c.2.2.2
                                  linarith only [hlam, p2155_0]
                              · linarith only [h1752, h2146, h2154, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1752, h2140, h2150, h2153, hc24, hlam, hphi, u4elo1]
                          · linarith only [h1752, h2140, h2145, h2152, hc23, hlam, hphi, ht34, u4elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2188 | h2188
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2189 | h2189
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2190 | h2190
                              · rcases h0bigk with h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h0, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1452, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1752, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1752, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2191_1, u4elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h0, h1452, h2140, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h0, h1752, h2140, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  rcases p2191_3 (m.d 0 1) (by simp) with h2201 | h2201
                                  · linarith only [h0, h2201, hlam]
                                  · linarith only [h2140, h2201, hlam]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2140, hc03, hc15, hlam, hphi, ht0b, ht5b, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2141, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1452, h2144, h2147, h2151, h2188, h2190, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  rcases p2191_3 (m.d 0 1) (by simp) with h2208 | h2208
                                  · linarith only [h1452, h2208, hlam]
                                  · linarith only [h2140, h2208, hlam]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2140, h2149, h2188, h2190, hc04, hc45, hlam, hphi, ht0b, ht5b, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2142, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2144, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1752, h2140, h2149, h2188, h2190, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2191_1, u4elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2140, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2143, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2145, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2146, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                              · linarith only [h2151, h2188, h2190, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h2146, h2189, hc24, hlam, hphi, u4elo0]
                          · linarith only [h1752, h2140, h2145, h2188, hc23, hlam, hphi, ht34, u4elo1]
                      · linarith only [h1752, h2140, h2149, h2150, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h0, h2143, h2149, hlam]
                  · linarith only [h1452, h2144, h2147, h2148, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h2141, h2147, hlam]
              · linarith only [h1752, h2140, h2146, hlam]
            · linarith only [h1752, h2140, h2144, h2145, hc34, hlam, hphi, u4elo1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2230 | h2230
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2231 | h2231
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2232 | h2232
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2233 | h2233
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2234 | h2234
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2235 | h2235
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2236 | h2236
                        · linarith only [h0, h1452, h2141, h2144, h2236, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2238 | h2238
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2239 | h2239
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2240 | h2240
                              · rcases h0bigk with h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h0, hlam, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h1452, hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h1752, hlam, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h1452, h2144, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2241_1, u4elo3]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h0, h1452, h2140, h2234, h2238, h2240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h0, h1452, h2140, h2144, h2234, h2238, h2240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  rcases p2241_3 (m.d 0 1) (by simp) with h2251 | h2251
                                  · linarith only [h0, h2251, hlam]
                                  · linarith only [h2140, h2251, hlam]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2140, h2144, h2234, h2238, h2240, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2241_1, u4elo3]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2141, hlam, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2144, hlam, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2140, h2144, h2234, h2238, h2240, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2241_1, u4elo3]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2140, h2234, h2238, h2240, hc04, hc45, hlam, hphi, ht0b, ht5b, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2142, hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h1752, hc03, hlam, hphi, ht34, p2241_1, u4elo1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h1752, h2140, h2234, h2238, h2240, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2241_1, u4elo1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2140, hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2143, hlam, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2230, hlam, p2241_0]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [h2231, hlam, p2241_1]
                                · have p2241_0 := h2241c.1
                                  have p2241_1 := h2241c.2.1
                                  have p2241_2 := h2241c.2.2.1
                                  have p2241_3 := h2241c.2.2.2
                                  linarith only [hlam, p2241_0]
                              · linarith only [h1452, h2140, h2144, h2234, h2240, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h1752, h2140, h2235, h2239, hc24, hlam, hphi, u4elo1]
                          · linarith only [h2144, h2230, h2238, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h1752, h2235, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2143, h2234, hlam]
                  · linarith only [h0, h2140, h2233, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                · linarith only [h0, h2141, h2232, hlam]
              · linarith only [h1752, h2140, h2231, hlam]
            · linarith only [h1452, h2140, h2230, hlam]
        · linarith only [h1752, h2140, h2141, h2143, hc23, hlam, hphi, ht34, u4elo1]
      · linarith only [h2141, h2142, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2280 | h2280
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2281 | h2281
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2282 | h2282
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2283 | h2283
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2284 | h2284
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2285 | h2285
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2286 | h2286
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2287 | h2287
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2288 | h2288
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2289 | h2289
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2290 | h2290
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2291 | h2291
                            · linarith only [h2141, h2280, h2285, h2291, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2141, h2280, h2284, h2285, h2291, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h2140, h2141, h2283, h2287, h2290, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1752, h2140, h2141, h2280, h2287, h2289, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h1752, h2140, h2287, h2288, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h2141, h2285, h2287, hc02, hc25, hlam, hphi]
                  · linarith only [h2141, h2280, h2285, h2286, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2299 | h2299
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2300 | h2300
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2301 | h2301
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2302 | h2302
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2303 | h2303
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2304 | h2304
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2305 | h2305
                              · rcases h0bigk with h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h0, hlam, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h1452, hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h1752, hlam, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h1752, h2299, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h0, h2285, hc01, hc23, hlam, hphi, ht12, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2141, hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h0, h2285, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h0, h2140, h2285, h2300, h2303, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2140, h2141, h2300, h2303, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2141, hc02, hc23, hlam, hphi, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h1752, h2140, h2141, h2300, h2303, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  rcases p2306_3 (m.d 0 1) (by simp) with h2321 | h2321
                                  · linarith only [h1452, h2321, hlam]
                                  · linarith only [h2140, h2321, hlam]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2140, h2300, h2303, h2305, hc04, hc45, hlam, hphi, ht0b, ht5b, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2280, hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2282, hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h1752, h2140, h2300, h2303, h2305, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2306_1, u4elo1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2140, hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2281, hlam, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2283, hlam, p2306_0]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [h2284, hlam, p2306_1]
                                · have p2306_0 := h2306c.1
                                  have p2306_1 := h2306c.2.1
                                  have p2306_2 := h2306c.2.2.1
                                  have p2306_3 := h2306c.2.2.2
                                  linarith only [hlam, p2306_0]
                              · linarith only [h1752, h2284, h2305, hc34, hlam, hphi, u4elo1]
                            · linarith only [h0, h2140, h2285, h2301, h2304, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h2285, h2303, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h1752, h2140, h2285, h2299, h2301, h2302, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1752, h2301, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2281, h2300, hlam]
                  · linarith only [h0, h2140, h2299, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1752, h2140, h2284, hlam]
            · linarith only [h1452, h2140, h2283, hlam]
          · linarith only [h2141, h2280, h2282, hc24, hlam, hphi, u4elo3]
        · linarith only [h1752, h2140, h2280, h2281, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2345 | h2345
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2346 | h2346
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2347 | h2347
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2348 | h2348
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2349 | h2349
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2350 | h2350
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2351 | h2351
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2352 | h2352
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2353 | h2353
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2354 | h2354
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2355 | h2355
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2356 | h2356
                              · rcases h0bigk with h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h0, hlam, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h1452, hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h1752, hlam, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h0, h2280, h2350, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2357_1, u4elo1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2280, h2350, hc01, hlam, hphi, ht12, ht23, ht34, p2357_1, u4elo1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2141, hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2280, hlam, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2140, h2280, h2350, h2351, h2354, h2356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2357_1, u4elo1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2140, h2351, h2354, h2356, hc03, hc45, hlam, hphi, ht0b, ht5b, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2141, h2349, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h0, h2140, h2141, h2280, h2349, h2351, h2354, h2356, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2140, h2141, h2349, h2351, h2354, h2356, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2140, h2351, h2354, h2356, hc04, hc45, hlam, hphi, ht0b, ht5b, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h0, h2140, h2280, h2350, h2351, h2354, h2356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2357_1, u4elo1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2346, hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2140, h2280, h2350, h2351, h2354, h2356, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2357_1, u4elo1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2140, hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2345, hlam, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2347, hlam, p2357_0]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [h2348, hlam, p2357_1]
                                · have p2357_0 := h2357c.1
                                  have p2357_1 := h2357c.2.1
                                  have p2357_2 := h2357c.2.2.1
                                  have p2357_3 := h2357c.2.2.2
                                  linarith only [hlam, p2357_0]
                              · linarith only [h2280, h2348, h2350, h2356, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1752, h2140, h2280, h2352, h2355, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2141, h2347, h2354, hlam]
                        · linarith only [h0, h2141, h2353, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h1752, h2140, h2351, h2352, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h2141, h2345, h2351, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h2141, h2349, h2350, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2390 | h2390
                  · linarith only [h0, h2140, h2280, h2349, h2390, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2140, h2390, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h0, h2140, h2280, h2348, hlam]
            · linarith only [h1452, h2140, h2347, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2395 | h2395
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2396 | h2396
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2397 | h2397
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2398 | h2398
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2399 | h2399
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2400 | h2400
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2401 | h2401
                        · linarith only [h0, h2140, h2141, h2346, h2397, h2399, h2401, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h2140, h2141, h2399, h2401, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h1752, h2140, h2399, h2400, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h2141, h2345, h2399, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h2141, h2397, h2398, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2407 | h2407
                  · linarith only [h0, h2140, h2280, h2397, h2407, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2140, h2407, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1452, h2140, h2346, h2396, hlam]
            · linarith only [h0, h2140, h2141, h2395, hlam]
        · linarith only [h0, h2140, h2345, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2413 | h2413
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2414 | h2414
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2415 | h2415
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2416 | h2416
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2417 | h2417
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2418 | h2418
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2419 | h2419
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2420 | h2420
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2421 | h2421
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2422 | h2422
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2423 | h2423
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2424 | h2424
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2425 | h2425
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2426 | h2426
                              · rcases h0bigk with h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h0, hlam, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h1452, hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h1752, hlam, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2140, hlam, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h0, h2413, h2423, h2426, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h0, h2414, h2423, h2426, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h0, h2140, hc01, hc12, hlam, hphi, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h1452, h2419, hc01, hc12, hlam, hphi, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2413, hlam, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h1452, h2414, h2419, h2423, h2426, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h1452, h2140, h2419, hc01, hc12, hlam, hphi, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2427_1, u4elo0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2414, hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2416, hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h1752, h2140, hc01, hlam, hphi, ht12, ht23, ht34, p2427_1, u4elo1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2140, h2422, hc01, hlam, hphi, ht12, ht23, ht34, p2427_1, u4elo1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2415, hlam, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2417, hlam, p2427_0]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [h2418, hlam, p2427_1]
                                · have p2427_0 := h2427c.1
                                  have p2427_1 := h2427c.2.1
                                  have p2427_2 := h2427c.2.2.1
                                  have p2427_3 := h2427c.2.2.2
                                  linarith only [hlam, p2427_0]
                              · linarith only [h1752, h2418, h2426, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1752, h2418, h2423, h2425, hc34, hlam, hphi, u4elo1]
                          · linarith only [h2140, h2417, h2422, h2423, h2424, hc34, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2456 | h2456
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2457 | h2457
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2458 | h2458
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
                                  linarith only [h0, hlam, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h1452, hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h1752, hlam, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2140, hlam, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h0, h1452, hc01, hc12, hlam, hphi, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h0, h1752, hc01, hc12, hlam, hphi, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h0, h2140, hc01, hc12, hlam, hphi, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h1452, h2419, hc01, hc12, hlam, hphi, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2413, hlam, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h1452, h2414, h2419, h2423, h2456, h2458, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h1452, h2140, h2419, hc01, hc12, hlam, hphi, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2459_1, u4elo0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2414, hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2416, hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h1752, h2140, hc01, hlam, hphi, ht12, ht23, ht34, p2459_1, u4elo1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2140, h2422, hc01, hlam, hphi, ht12, ht23, ht34, p2459_1, u4elo1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2415, hlam, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2417, hlam, p2459_0]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [h2418, hlam, p2459_1]
                                · have p2459_0 := h2459c.1
                                  have p2459_1 := h2459c.2.1
                                  have p2459_2 := h2459c.2.2.1
                                  have p2459_3 := h2459c.2.2.2
                                  linarith only [hlam, p2459_0]
                              · linarith only [h1752, h2418, h2458, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1752, h2418, h2457, hc24, hlam, hphi, u4elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2487 | h2487
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2488 | h2488
                              · rcases h0bigk with h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h0, hlam, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h1452, hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h1752, hlam, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2140, hlam, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h0, h1452, hc01, hc12, hlam, hphi, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h0, h1752, hc01, hc12, hlam, hphi, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h0, h2417, h2456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h1452, h2419, hc01, hc12, hlam, hphi, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2413, hlam, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h1452, h2414, h2419, h2487, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h1452, h2417, h2419, h2456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2489_1, u4elo0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2414, hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2416, hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h1752, h2417, h2456, hc23, hlam, hphi, ht34, p2489_1, u4elo1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2140, hc01, hc15, hlam, hphi, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2415, hlam, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2417, hlam, p2489_0]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [h2418, hlam, p2489_1]
                                · have p2489_0 := h2489c.1
                                  have p2489_1 := h2489c.2.1
                                  have p2489_2 := h2489c.2.2.1
                                  have p2489_3 := h2489c.2.2.2
                                  linarith only [hlam, p2489_0]
                              · linarith only [h2423, h2488, hc23, hlam, hphi, ht34, u4elo4]
                            · linarith only [h1752, h2418, h2487, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2418, h2422, hlam]
                    · linarith only [h0, h2415, h2421, hlam]
                  · linarith only [h1452, h2416, h2419, h2420, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h2413, h2419, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2521 | h2521
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2522 | h2522
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2523 | h2523
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2524 | h2524
                      · linarith only [h2418, h2524, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2524, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2415, h2523, hlam]
                  · linarith only [h0, h2414, h2522, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                · linarith only [h0, h2413, h2521, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2530 | h2530
              · linarith only [h2416, h2417, h2530, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2532 | h2532
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2533 | h2533
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2534 | h2534
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2535 | h2535
                      · linarith only [h2530, h2535, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2535, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2415, h2534, hlam]
                  · linarith only [h0, h2414, h2533, hlam]
                · linarith only [h0, h2413, h2532, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2541 | h2541
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2542 | h2542
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2543 | h2543
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2544 | h2544
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2545 | h2545
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2546 | h2546
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2547 | h2547
                        · linarith only [h2413, h2416, h2541, h2547, hc02, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2549 | h2549
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2550 | h2550
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2551 | h2551
                              · rcases h0bigk with h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h0, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h1452, hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h1752, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2140, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h0, h2413, h2549, h2551, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h0, h2413, h2416, h2549, h2551, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h0, h2140, hc01, hc12, hlam, hphi, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2416, hc01, hc34, hlam, hphi, ht12, ht23, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2413, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2416, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2140, h2416, hc01, hlam, hphi, ht12, ht23, ht34, p2552_1, u4elo3]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h1752, hc01, hlam, hphi, ht12, ht23, ht34, p2552_1, u4elo1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2414, hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h1752, hc03, hlam, hphi, ht34, p2552_1, u4elo1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h1752, h2140, hc01, hlam, hphi, ht12, ht23, ht34, p2552_1, u4elo1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2140, hc01, hc15, hlam, hphi, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2415, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2541, hlam, p2552_0]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [h2542, hlam, p2552_1]
                                · have p2552_0 := h2552c.1
                                  have p2552_1 := h2552c.2.1
                                  have p2552_2 := h2552c.2.2.1
                                  have p2552_3 := h2552c.2.2.2
                                  linarith only [hlam, p2552_0]
                              · linarith only [h2416, h2551, hc03, hlam, hphi, ht34, u4elo4]
                            · linarith only [h2416, h2541, h2542, h2550, hc24, hlam, hphi, u4elo3]
                          · linarith only [h2416, h2541, h2549, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h1752, h2416, h2541, h2542, h2546, hc04, hlam, hphi, u4elo3]
                    · linarith only [h0, h2415, h2416, h2541, h2545, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1452, h2543, h2544, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2413, h2543, hlam]
              · linarith only [h2416, h2541, h2542, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2586 | h2586
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2587 | h2587
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2588 | h2588
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2589 | h2589
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2590 | h2590
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2591 | h2591
                        · linarith only [h0, h1452, h2413, h2416, h2591, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2593 | h2593
                          · linarith only [h2413, h2541, h2593, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2595 | h2595
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2596 | h2596
                              · rcases h0bigk with h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [hlam, p2597_0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h0, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h1452, hlam, p2597_0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h1752, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2140, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [hlam, p2597_0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h0, h1452, hc01, hc12, hlam, hphi, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h0, h2414, h2595, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h0, h1452, h2541, hc01, hc12, hlam, hphi, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2541, h2596, hc01, hc34, hlam, hphi, ht12, ht23, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2413, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [hlam, p2597_0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2416, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2541, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2597_1, u4elo0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2414, hlam, p2597_0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h1752, hc03, hlam, hphi, ht34, p2597_1, u4elo1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [hlam, p2597_0]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h1752, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2597_1, u4elo1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2140, h2590, hc01, hlam, hphi, ht12, ht23, ht34, p2597_1, u4elo1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2415, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h1452, h2140, h2590, hc01, hlam, hphi, ht12, ht23, ht34, p2597_1, u4elo1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [h2586, hlam, p2597_1]
                                · have p2597_0 := h2597c.1
                                  have p2597_1 := h2597c.2.1
                                  have p2597_2 := h2597c.2.2.1
                                  have p2597_3 := h2597c.2.2.2
                                  linarith only [hlam, p2597_0]
                              · linarith only [h2595, h2596, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1752, h2586, h2595, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2586, h2590, hlam]
                    · linarith only [h0, h2415, h2589, hlam]
                  · linarith only [h0, h2588, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2413, h2587, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2629 | h2629
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2630 | h2630
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2631 | h2631
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2632 | h2632
                      · linarith only [h2586, h2632, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2632, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2415, h2631, hlam]
                  · linarith only [h0, h2414, h2630, hlam]
                · linarith only [h0, h2413, h2414, h2416, h2629, hc24, hlam, hphi, u4elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2638 | h2638
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2639 | h2639
            · linarith only [h2413, h2415, h2639, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2641 | h2641
              · linarith only [h2414, h2415, h2641, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2643 | h2643
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2644 | h2644
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2645 | h2645
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2646 | h2646
                      · linarith only [h2641, h2646, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2646, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2649 | h2649
                      · linarith only [h1752, h2641, h2649, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1752, h2649, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1452, h2643, h2644, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2413, h2643, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2654 | h2654
            · linarith only [h2413, h2415, h2654, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2656 | h2656
              · linarith only [h2414, h2415, h2656, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2658 | h2658
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2659 | h2659
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2660 | h2660
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2661 | h2661
                      · linarith only [h1452, h2638, h2656, h2661, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1752, h2661, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2664 | h2664
                      · linarith only [h1452, h2638, h2656, h2664, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1752, h2664, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2659, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h2413, h2415, h2656, h2658, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h2413, h2414, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2670 | h2670
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2671 | h2671
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2672 | h2672
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2673 | h2673
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2674 | h2674
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2675 | h2675
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2676 | h2676
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2677 | h2677
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2678 | h2678
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2679 | h2679
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2680 | h2680
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2681 | h2681
                            · linarith only [h2413, h2670, h2675, h2681, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2674, h2681, hc24, hlam, hphi, u4elo0]
                          · linarith only [h2413, h2670, h2673, h2679, h2680, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h2413, h2670, h2679, hc24, hlam, hphi, u4elo3]
                      · linarith only [h2413, h2670, h2674, h2675, h2678, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2413, h2671, h2675, h2677, hlam]
                  · linarith only [h2413, h2670, h2675, h2676, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2689 | h2689
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2690 | h2690
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2691 | h2691
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2692 | h2692
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2693 | h2693
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2694 | h2694
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2695 | h2695
                              · rcases h0bigk with h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h0, hlam, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h1452, hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h1752, hlam, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2140, hlam, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2413, hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h0, h2675, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h0, h2140, h2675, hc01, hc23, hlam, hphi, ht12, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2413, hc01, hc23, hlam, hphi, ht12, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2413, hc02, hc23, hlam, hphi, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2413, h2670, h2692, h2695, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2140, h2413, hc01, hc23, hlam, hphi, ht12, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2696_1, u4elo0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2670, hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2672, hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h1752, h2140, hc01, hlam, hphi, ht12, ht23, ht34, p2696_1, u4elo1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2140, hc01, hc15, hlam, hphi, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2671, hlam, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2673, hlam, p2696_0]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [h2674, hlam, p2696_1]
                                · have p2696_0 := h2696c.1
                                  have p2696_1 := h2696c.2.1
                                  have p2696_2 := h2696c.2.2.1
                                  have p2696_3 := h2696c.2.2.2
                                  linarith only [hlam, p2696_0]
                              · linarith only [h1752, h2674, h2695, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1752, h2674, h2694, hc24, hlam, hphi, u4elo1]
                          · linarith only [h0, h2675, h2693, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h2675, h2692, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1752, h2691, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2671, h2690, hlam]
                  · linarith only [h0, h2670, h2689, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2729 | h2729
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2730 | h2730
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2731 | h2731
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2732 | h2732
                      · linarith only [h2674, h2732, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2732, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h2413, h2671, h2729, h2731, hlam]
                  · linarith only [h2413, h2670, h2729, h2730, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2737 | h2737
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2738 | h2738
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2739 | h2739
                      · linarith only [h1752, h2674, h2729, h2737, h2739, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1752, h2739, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2671, h2738, hlam]
                  · linarith only [h0, h2737, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h2413, h2671, h2673, hlam]
          · linarith only [h2413, h2670, h2672, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2746 | h2746
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2747 | h2747
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2748 | h2748
              · linarith only [h2670, h2671, h2748, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2750 | h2750
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2751 | h2751
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2752 | h2752
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2753 | h2753
                      · linarith only [h2748, h2753, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2753, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h2413, h2670, h2750, h2752, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2413, h2670, h2750, h2751, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2758 | h2758
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2759 | h2759
                    · linarith only [h2670, h2671, h2750, h2759, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2761 | h2761
                      · linarith only [h1752, h2748, h2761, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1752, h2761, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2758, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2765 | h2765
              · linarith only [h2670, h2671, h2765, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2767 | h2767
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2768 | h2768
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2769 | h2769
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2770 | h2770
                      · linarith only [h2765, h2770, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2770, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h2413, h2670, h2767, h2769, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2413, h2670, h2767, h2768, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2775 | h2775
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2776 | h2776
                    · linarith only [h2670, h2671, h2767, h2776, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2778 | h2778
                      · linarith only [h1752, h2765, h2778, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1752, h2778, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2775, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h2413, h2670, h2746, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2783 | h2783
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2784 | h2784
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2785 | h2785
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2786 | h2786
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2787 | h2787
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2788 | h2788
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2789 | h2789
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2790 | h2790
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2791 | h2791
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2792 | h2792
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2793 | h2793
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2794 | h2794
                              · rcases h0bigk with h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c | h2795c
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h0, hlam, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h1452, hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h1752, hlam, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2140, hlam, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2670, h2788, hc01, hlam, hphi, ht12, ht23, ht34, p2795_1, u4elo1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2413, hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2670, hlam, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2670, h2788, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2795_1, u4elo1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h1452, hc01, hc13, hlam, hphi, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2413, h2787, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2413, h2670, h2783, h2787, h2788, h2792, hc04, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2795_1, u4elo1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2140, h2413, h2787, hc01, hc12, hlam, hphi, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2795_1, u4elo0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2783, h2792, hc04, hc35, hlam, hphi, ht0b, ht5b, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2784, hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2140, h2670, h2788, hc01, hlam, hphi, ht12, ht23, ht34, p2795_1, u4elo1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2140, h2790, hc01, hlam, hphi, ht12, ht23, ht34, p2795_1, u4elo1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2783, hlam, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2785, hlam, p2795_0]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [h2786, hlam, p2795_1]
                                · have p2795_0 := h2795c.1
                                  have p2795_1 := h2795c.2.1
                                  have p2795_2 := h2795c.2.2.1
                                  have p2795_3 := h2795c.2.2.2
                                  linarith only [hlam, p2795_0]
                              · linarith only [h2670, h2786, h2788, h2794, hc34, hlam, hphi, u4elo1]
                            · linarith only [h2670, h2783, h2786, h2793, hlam]
                          · linarith only [h2413, h2785, h2792, hlam]
                        · linarith only [h2413, h2791, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1752, h2790, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2783, h2789, hlam]
                  · linarith only [h2413, h2787, h2788, hc02, hlam, hphi, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2828 | h2828
                  · linarith only [h2670, h2783, h2787, h2828, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2828, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2670, h2783, h2786, hlam]
            · linarith only [h2670, h2783, h2784, h2785, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2833 | h2833
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2834 | h2834
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2835 | h2835
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2836 | h2836
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2837 | h2837
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2838 | h2838
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2839 | h2839
                        · linarith only [h2784, h2833, h2835, h2839, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2140, h2413, h2783, h2839, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2834, h2836, h2838, hc24, hlam, hphi, u4elo0]
                    · linarith only [h2413, h2783, h2784, h2837, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h2140, h2413, h2783, h2835, h2836, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2845 | h2845
                  · linarith only [h2140, h2670, h2783, h2835, h2845, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2845, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2670, h2783, h2834, hlam]
            · linarith only [h2413, h2783, h2833, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2850 | h2850
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2851 | h2851
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2852 | h2852
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2853 | h2853
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2854 | h2854
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2855 | h2855
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2856 | h2856
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2857 | h2857
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2858 | h2858
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2859 | h2859
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2860 | h2860
                              · rcases h0bigk with h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h1452, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h1752, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2140, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2783, h2853, h2857, h2859, hc01, hc12, hlam, hphi, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2413, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2670, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2783, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h1452, hc01, hc13, hlam, hphi, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2413, h2853, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2413, h2853, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2413, h2853, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2861_1, u4elo0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, h1752, hc01, hlam, hphi, ht12, ht23, ht34, p2861_1, u4elo1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2850, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, h1752, h2783, hc01, hlam, hphi, ht12, ht23, ht34, p2861_1, u4elo1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2140, h2856, hc01, hlam, hphi, ht12, ht23, ht34, p2861_1, u4elo1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h0, h2140, h2856, hc01, hlam, hphi, ht12, ht23, ht34, p2861_1, u4elo1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2851, hlam, p2861_0]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [h2852, hlam, p2861_1]
                                · have p2861_0 := h2861c.1
                                  have p2861_1 := h2861c.2.1
                                  have p2861_2 := h2861c.2.2.1
                                  have p2861_3 := h2861c.2.2.2
                                  linarith only [hlam, p2861_0]
                              · linarith only [h2670, h2852, h2854, h2860, hc34, hlam, hphi, u4elo1]
                            · linarith only [h2670, h2852, h2859, hlam]
                          · linarith only [h2413, h2851, h2858, hlam]
                        · linarith only [h0, h2413, h2857, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2670, h2852, h2854, h2856, hlam]
                    · linarith only [h0, h2413, h2853, h2855, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2413, h2853, h2854, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2894 | h2894
                  · linarith only [h0, h2670, h2853, h2894, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2894, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2897 | h2897
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2898 | h2898
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2899 | h2899
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2900 | h2900
                      · linarith only [h2852, h2900, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2900, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2413, h2897, h2899, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2413, h2897, h2898, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2905 | h2905
                  · linarith only [h0, h2670, h2897, h2905, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2905, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2908 | h2908
              · linarith only [h2850, h2851, h2908, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2910 | h2910
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2911 | h2911
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2912 | h2912
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2913 | h2913
                      · linarith only [h2908, h2913, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1752, h2913, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2670, h2911, h2912, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h2413, h2910, h2911, hc03, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2918 | h2918
                  · linarith only [h0, h2670, h2910, h2918, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2918, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2921 | h2921
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2922 | h2922
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2923 | h2923
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2924 | h2924
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2925 | h2925
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2926 | h2926
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2927 | h2927
                        · linarith only [h0, h2783, h2850, h2921, h2923, h2927, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2413, h2927, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2922, h2926, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h2413, h2923, h2925, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2413, h2923, h2924, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2933 | h2933
                  · linarith only [h0, h2670, h2923, h2933, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2850, h2921, h2922, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2937 | h2937
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2938 | h2938
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2939 | h2939
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2940 | h2940
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2941 | h2941
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2942 | h2942
                        · linarith only [h0, h2413, h2850, h2938, h2942, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2413, h2942, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2937, h2939, h2941, hc24, hlam, hphi, u4elo0]
                    · linarith only [h0, h2413, h2938, h2940, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2413, h2938, h2939, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2948 | h2948
                  · linarith only [h0, h2670, h2938, h2948, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2948, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2951 | h2951
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2952 | h2952
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2953 | h2953
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2954 | h2954
                      · linarith only [h0, h2413, h2850, h2937, h2954, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1752, h2954, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2413, h2951, h2953, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2413, h2951, h2952, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2959 | h2959
                  · linarith only [h0, h2670, h2951, h2959, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2959, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1452 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1752 | h1752
  · exact r1l7_20_12_14_H_I_L_I_L_0_x1_x1_x0 m hb0 hb2 hb4 h0 h1452 h1752
  · exact r1l7_20_12_14_H_I_L_I_L_0_x1_x1_x1 m hb0 hb2 hb4 h0 h1452 h1752

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1452 | h1452
  · exact r1l7_20_12_14_H_I_L_I_L_0_x1_x0 m hb0 hb2 hb4 h0 h1452
  · exact r1l7_20_12_14_H_I_L_I_L_0_x1_x1 m hb0 hb2 hb4 h0 h1452

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_I_L_0_x1 m hb0 hb2 hb4 h0

end R2N4
