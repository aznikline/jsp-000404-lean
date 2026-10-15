import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S9
import Jsp000404.R1LeavesN7_50S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1367 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1500 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1645 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2144 | h2144
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2145 | h2145
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2146 | h2146
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2147 | h2147
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2148 | h2148
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2149 | h2149
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2150 | h2150
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2151 | h2151
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2152 | h2152
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2153 | h2153
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2154 | h2154
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2155 | h2155
                        · rcases h5bigk with h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h1500, hlam, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h1645, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2146, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2156_1, u3ehi4]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h1645, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h0, h1645, h2148, hc01, hc12, hlam, hphi, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2150, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2156_1, u3ehi4]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            rcases p2156_3 (m.d 0 5) (by simp) with h2166 | h2166
                            · linarith only [h1500, h2166, hlam]
                            · linarith only [h2146, h2166, hlam]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2145, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2156_1, u3ehi4]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2148, hlam, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2147, h2153, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2156_1, u3ehi4]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2147, h2152, h2154, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2145, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2150, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2153, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h1645, h2145, h2147, h2152, h2154, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2156_1]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2146, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2151, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2154, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [h2155, hlam, p2156_0]
                          · have p2156_0 := h2156c.1
                            have p2156_1 := h2156c.2.1
                            have p2156_2 := h2156c.2.2.1
                            have p2156_3 := h2156c.2.2.2
                            linarith only [hlam, p2156_0]
                        · linarith only [h2147, h2152, h2154, h2155, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1645, h2146, h2154, hlam]
                    · linarith only [h2152, h2153, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2187 | h2187
                    · linarith only [h2152, h2187, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1645, h2145, h2187, hlam]
                · linarith only [h1500, h2146, h2151, hlam]
              · linarith only [h1367, h2144, h2150, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1367, h2144, h2149, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2193 | h2193
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2194 | h2194
              · linarith only [h2147, h2148, h2194, hlam]
              · linarith only [h1367, h2145, h2194, hlam]
            · linarith only [h1367, h2144, h2193, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2198 | h2198
          · linarith only [h0, h1645, h2147, h2198, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2200 | h2200
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2201 | h2201
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2202 | h2202
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2203 | h2203
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2204 | h2204
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2205 | h2205
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2206 | h2206
                        · rcases h5bigk with h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h1500, hlam, p2207_1]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h1645, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2144, h2146, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2207_1, u3ehi4]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            rcases p2207_3 (m.d 0 5) (by simp) with h2212 | h2212
                            · rcases p2207_3 (m.d 1 5) (by simp) with h2213 | h2213
                              · rcases p2207_3 (m.d 2 5) (by simp) with h2214 | h2214
                                · rcases p2207_3 (m.d 3 5) (by simp) with h2215 | h2215
                                  · linarith only [h2145, h2215, hlam]
                                  · linarith only [h2206, h2215, hlam]
                                · linarith only [h2205, h2214, hlam]
                              · linarith only [h2202, h2213, hlam]
                            · linarith only [h2146, h2212, hlam]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h1500, h2202, hc01, hc14, hlam, hphi, p2207_1]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2198, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2198, h2203, h2205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2207_1, u3ehi4]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            rcases p2207_3 (m.d 0 5) (by simp) with h2225 | h2225
                            · linarith only [h1500, h2225, hlam]
                            · linarith only [h2146, h2225, hlam]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2145, h2203, h2205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2207_1, u3ehi4]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h1500, h2203, h2205, hc01, hc23, hlam, hphi, ht12, p2207_1]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2203, h2205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2207_1, u3ehi4]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            rcases p2207_3 (m.d 0 5) (by simp) with h2232 | h2232
                            · linarith only [h1645, h2232, hlam]
                            · linarith only [h2146, h2232, hlam]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2145, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2201, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2204, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h1367, h2144, h2147, h2206, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2207_1]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2146, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2202, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2205, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [h2206, hlam, p2207_0]
                          · have p2207_0 := h2207c.1
                            have p2207_1 := h2207c.2.1
                            have p2207_2 := h2207c.2.2.1
                            have p2207_3 := h2207c.2.2.2
                            linarith only [hlam, p2207_0]
                        · rcases h5bigk with h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c | h2245c
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h1500, hlam, p2245_1]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h1645, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2245_1, u3ehi4]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h1367, h2144, h2146, h2147, h2206, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2245_1]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p2245_1]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2198, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2198, h2203, h2205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2245_1, u3ehi4]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2198, h2203, h2205, h2206, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2245_1, u3ehi3]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2146, h2203, h2205, h2206, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2245_1, u3ehi3]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h1500, h2203, h2205, hc01, hc23, hlam, hphi, ht12, p2245_1]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2203, h2205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2245_1, u3ehi4]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2203, h2205, h2206, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2245_1, u3ehi3]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2145, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2201, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2204, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2206, hlam, p2245_1]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2146, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2202, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2205, hlam, p2245_0]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [h2146, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2245_1, u3ehi4]
                          · have p2245_0 := h2245c.1
                            have p2245_1 := h2245c.2.1
                            have p2245_2 := h2245c.2.2.1
                            have p2245_3 := h2245c.2.2.2
                            linarith only [hlam, p2245_0]
                      · linarith only [h1645, h2146, h2205, hlam]
                    · linarith only [h1367, h2144, h2147, h2204, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1367, h2144, h2147, h2203, hlam]
                · linarith only [h1500, h2146, h2202, hlam]
              · linarith only [h1367, h2145, h2201, hlam]
            · linarith only [h1367, h2145, h2200, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2277 | h2277
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2278 | h2278
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2279 | h2279
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2280 | h2280
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2281 | h2281
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2282 | h2282
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2283 | h2283
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2284 | h2284
                      · linarith only [h2144, h2146, h2277, h2282, h2284, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2286 | h2286
                        · linarith only [h2144, h2146, h2286, hlam]
                        · rcases h5bigk with h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c | h2288c
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h1500, hlam, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h1645, hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h1645, h2284, hc45, hlam, hphi, ht34, p2288_1, u3ehi4]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2146, hlam, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h0, h1645, h2278, hc01, hc12, hlam, hphi, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2277, h2280, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2288_1, u3ehi4]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2277, h2279, h2281, h2284, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2144, h2146, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2288_1, u3ehi3]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2278, hlam, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2277, h2283, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2288_1, u3ehi4]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2284, hlam, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2145, hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2280, hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2283, hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2286, hlam, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2144, h2146, hc45, hlam, hphi, ht34, p2288_1, u3ehi3]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2281, hlam, p2288_0]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2277, h2279, h2281, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2288_1]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [h2277, h2279, h2281, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2288_1, u3ehi4]
                          · have p2288_0 := h2288c.1
                            have p2288_1 := h2288c.2.1
                            have p2288_2 := h2288c.2.2.1
                            have p2288_3 := h2288c.2.2.2
                            linarith only [hlam, p2288_0]
                    · linarith only [h2282, h2283, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2144, h2146, h2277, h2279, h2281, h2282, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2316 | h2316
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2317 | h2317
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2318 | h2318
                      · linarith only [h2144, h2146, h2277, h2316, h2318, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2320 | h2320
                        · linarith only [h2144, h2146, h2320, hlam]
                        · rcases h5bigk with h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h1500, hlam, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h1645, hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2322_1, u3ehi4]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2146, hlam, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h1500, h2281, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h0, h1645, h2281, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2281, hc45, hlam, hphi, ht34, p2322_1, u3ehi4]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2281, hlam, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2144, h2146, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2322_1, u3ehi3]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2278, hlam, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2277, h2317, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2322_1, u3ehi4]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2318, hlam, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2145, hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2280, hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2317, hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hlam, p2322_0]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2320, hlam, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h2144, h2146, hc45, hlam, hphi, ht34, p2322_1, u3ehi3]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h1500, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [h0, h1645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2322_1]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p2322_1, u3ehi4]
                          · have p2322_0 := h2322c.1
                            have p2322_1 := h2322c.2.1
                            have p2322_2 := h2322c.2.2.1
                            have p2322_3 := h2322c.2.2.2
                            linarith only [hlam, p2322_0]
                    · linarith only [h1367, h2145, h2277, h2316, h2317, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h2144, h2146, h2316, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1367, h2145, h2280, hlam]
            · linarith only [h1367, h2144, h2146, h2279, hc45, hlam, hphi, ht34, u3ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2352 | h2352
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2353 | h2353
              · linarith only [h2277, h2278, h2353, hlam]
              · linarith only [h1367, h2145, h2353, hlam]
            · linarith only [h1367, h2144, h2352, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2357 | h2357
          · linarith only [h0, h1645, h2277, h2357, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2359 | h2359
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2360 | h2360
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2361 | h2361
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2362 | h2362
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2363 | h2363
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2364 | h2364
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2365 | h2365
                        · linarith only [h2144, h2146, h2365, hlam]
                        · rcases h5bigk with h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h1500, hlam, p2367_1]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h1645, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2365, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2146, hlam, p2367_1]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p2367_1]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2357, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2357, h2362, h2364, h2365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2144, h2146, h2357, h2362, h2364, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2145, h2362, h2364, h2365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h1500, h2362, h2364, hc01, hc23, hlam, hphi, ht12, p2367_1]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2362, h2364, h2365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2144, h2146, h2362, h2364, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2145, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2360, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2363, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2365, hlam, p2367_1]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2145, h2361, h2365, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2361, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2364, hlam, p2367_0]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [h2277, h2359, h2361, h2365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2367_1, u3ehi3]
                          · have p2367_0 := h2367c.1
                            have p2367_1 := h2367c.2.1
                            have p2367_2 := h2367c.2.2.1
                            have p2367_3 := h2367c.2.2.2
                            linarith only [hlam, p2367_0]
                      · linarith only [h0, h2277, h2357, h2359, h2361, h2364, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1367, h2145, h2277, h2363, hlam]
                  · linarith only [h2145, h2146, h2277, h2359, h2361, h2362, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2396 | h2396
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2397 | h2397
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2398 | h2398
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2399 | h2399
                        · linarith only [h2144, h2146, h2399, hlam]
                        · rcases h5bigk with h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h1500, hlam, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h1645, hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2399, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2146, hlam, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2357, hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2399, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2361, hlam, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2145, h2399, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h1500, hc01, hc25, hlam, hphi, ht12, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2397, h2399, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2144, h2146, h2396, h2398, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2145, hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2360, hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2397, hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2399, hlam, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2145, h2399, hc45, hlam, hphi, ht34, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h0, h2357, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2401_1]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2398, hlam, p2401_0]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [h2396, h2398, h2399, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2401_1, u3ehi3]
                          · have p2401_0 := h2401c.1
                            have p2401_1 := h2401c.2.1
                            have p2401_2 := h2401c.2.2.1
                            have p2401_3 := h2401c.2.2.2
                            linarith only [hlam, p2401_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2427 | h2427
                        · linarith only [h0, h1367, h1645, h2144, h2277, h2398, h2427, hc01, hc23, hlam, hphi, ht12]
                        · rcases h5bigk with h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h1500, hlam, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h1645, hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2429_1, u3ehi4]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2146, hlam, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2357, hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2429_1, u3ehi4]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2361, hlam, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2146, h2398, hc04, hc45, hlam, hphi, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h1500, h2398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2398, hc45, hlam, hphi, ht34, p2429_1, u3ehi4]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2398, hlam, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2145, hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2360, hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2397, hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hlam, p2429_0]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2427, hlam, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h2144, h2146, hc45, hlam, hphi, ht34, p2429_1, u3ehi3]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h1500, h2144, h2146, hc45, hlam, hphi, ht34, p2429_1, u3ehi3]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [h0, h1645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2429_1]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p2429_1, u3ehi4]
                          · have p2429_0 := h2429c.1
                            have p2429_1 := h2429c.2.1
                            have p2429_2 := h2429c.2.2.1
                            have p2429_3 := h2429c.2.2.2
                            linarith only [hlam, p2429_0]
                    · linarith only [h1367, h2144, h2277, h2397, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1500, h2144, h2146, h2277, h2396, hc01, hc15, hlam, hphi]
              · linarith only [h1367, h2145, h2360, hlam]
            · linarith only [h1367, h2144, h2359, hlam]
    · linarith only [h2144, h2145, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2460 | h2460
    · linarith only [h2144, h2460, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2462 | h2462
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2463 | h2463
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2464 | h2464
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2465 | h2465
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2466 | h2466
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2467 | h2467
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2468 | h2468
                  · linarith only [h2144, h2463, h2468, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2470 | h2470
                    · linarith only [h2460, h2465, h2468, h2470, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2472 | h2472
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2473 | h2473
                        · rcases h5bigk with h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h1500, hlam, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h1645, hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2460, hlam, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2144, h2462, h2463, h2465, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h1500, h2467, hc01, hc14, hlam, hphi, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h0, h1645, h2467, hc01, hc14, hlam, hphi, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2463, h2465, h2467, h2470, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2474_1, u3ehi2]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            rcases p2474_3 (m.d 0 5) (by simp) with h2484 | h2484
                            · linarith only [h1500, h2484, hlam]
                            · linarith only [h2462, h2484, hlam]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2460, h2472, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2474_1, u3ehi0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2464, hlam, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2470, hlam, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2464, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2460, hc35, hlam, hphi, p2474_1, u3ehi0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2466, hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2463, h2466, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2463, h2465, h2473, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2474_1]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2462, hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2467, hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2472, hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [h2473, hlam, p2474_0]
                          · have p2474_0 := h2474c.1
                            have p2474_1 := h2474c.2.1
                            have p2474_2 := h2474c.2.2.1
                            have p2474_3 := h2474c.2.2.2
                            linarith only [hlam, p2474_0]
                        · linarith only [h2144, h2473, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h2144, h2462, h2468, h2472, hc34, hlam, hphi, u3ehi2]
                · linarith only [h2144, h2465, h2467, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2465, h2466, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2506 | h2506
              · linarith only [h2465, h2506, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2508 | h2508
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2509 | h2509
                  · linarith only [h1367, h2465, h2509, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2511 | h2511
                    · linarith only [h2463, h2465, h2511, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2513 | h2513
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2514 | h2514
                        · rcases h5bigk with h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h1500, hlam, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h1645, hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2460, hlam, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h1645, h2464, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h1500, h2465, h2508, hc01, hc34, hlam, hphi, ht12, ht23, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h0, h1645, h2465, h2508, hc01, hc34, hlam, hphi, ht12, ht23, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2506, hlam, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            rcases p2515_3 (m.d 0 5) (by simp) with h2525 | h2525
                            · linarith only [h1500, h2525, hlam]
                            · linarith only [h2462, h2525, hlam]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2460, h2513, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2515_1, u3ehi0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2464, hlam, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2511, hlam, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2464, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2460, h2514, hc34, hlam, hphi, p2515_1, u3ehi0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h1500, h2514, hc01, hc34, hlam, hphi, ht12, ht23, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h0, h1645, h2514, hc01, hc34, hlam, hphi, ht12, ht23, p2515_1]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            rcases p2515_3 (m.d 0 5) (by simp) with h2537 | h2537
                            · linarith only [h2460, h2537, hlam]
                            · linarith only [h2462, h2537, hlam]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2462, hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2508, hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2513, hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [h2514, hlam, p2515_0]
                          · have p2515_0 := h2515c.1
                            have p2515_1 := h2515c.2.1
                            have p2515_2 := h2515c.2.2.1
                            have p2515_3 := h2515c.2.2.2
                            linarith only [hlam, p2515_0]
                        · linarith only [h2144, h2514, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h2144, h2462, h2509, h2513, hc34, hlam, hphi, u3ehi2]
                · linarith only [h2144, h2462, h2465, h2508, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2548 | h2548
            · linarith only [h2144, h2463, h2464, h2548, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2550 | h2550
              · linarith only [h2548, h2550, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2552 | h2552
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2553 | h2553
                  · linarith only [h1367, h2548, h2553, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2555 | h2555
                    · linarith only [h1367, h2463, h2550, h2555, hc01, hc12, hlam, hphi]
                    · linarith only [h2463, h2464, h2555, hc35, hlam, hphi, u3ehi2]
                · linarith only [h1367, h2144, h2462, h2548, h2552, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2559 | h2559
          · linarith only [h0, h1645, h2463, h2559, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2561 | h2561
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2562 | h2562
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2563 | h2563
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2564 | h2564
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2565 | h2565
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2566 | h2566
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2567 | h2567
                        · rcases h5bigk with h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h1500, hlam, p2568_1]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h1645, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2460, hlam, p2568_1]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2144, h2462, h2463, h2561, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2568_1]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h1500, h2563, hc01, hc14, hlam, hphi, p2568_1]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2559, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2460, h2559, h2566, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2568_1, u3ehi0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            rcases p2568_3 (m.d 0 5) (by simp) with h2578 | h2578
                            · linarith only [h1500, h2578, hlam]
                            · linarith only [h2462, h2578, hlam]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2460, h2564, h2566, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2568_1, u3ehi0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h1500, h2564, h2566, hc01, hc23, hlam, hphi, ht12, p2568_1]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2460, h2564, h2566, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2568_1, u3ehi0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            rcases p2568_3 (m.d 0 5) (by simp) with h2585 | h2585
                            · linarith only [h1645, h2585, hlam]
                            · linarith only [h2462, h2585, hlam]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2460, h2562, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2568_1, u3ehi0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2562, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2565, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2463, h2561, h2567, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2568_1]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2462, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2563, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2566, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [h2567, hlam, p2568_0]
                          · have p2568_0 := h2568c.1
                            have p2568_1 := h2568c.2.1
                            have p2568_2 := h2568c.2.2.1
                            have p2568_3 := h2568c.2.2.2
                            linarith only [hlam, p2568_0]
                        · linarith only [h2144, h2567, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h2144, h2564, h2566, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h2463, h2562, h2565, hlam]
                  · linarith only [h2463, h2562, h2564, hc34, hlam, hphi, u3ehi4]
                · linarith only [h2144, h2462, h2561, h2563, hlam]
              · linarith only [h2561, h2562, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2604 | h2604
              · linarith only [h2561, h2604, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2606 | h2606
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2607 | h2607
                  · linarith only [h1367, h2561, h2607, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2463, h2607, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1367, h2144, h2462, h2561, h2606, hc34, hlam, hphi, u3ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2611 | h2611
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2612 | h2612
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2613 | h2613
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2614 | h2614
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2615 | h2615
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2616 | h2616
                  · linarith only [h2144, h2611, h2616, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2618 | h2618
                    · linarith only [h2616, h2618, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2620 | h2620
                      · linarith only [h2144, h2462, h2611, h2613, h2616, h2620, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2622 | h2622
                        · linarith only [h2144, h2462, h2611, h2613, h2622, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2144, h2615, h2622, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h2144, h2613, h2615, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2144, h2613, h2614, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2627 | h2627
              · linarith only [h2613, h2627, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2629 | h2629
                · linarith only [h2144, h2462, h2613, h2629, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2631 | h2631
                  · linarith only [h2611, h2613, h2629, h2631, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2633 | h2633
                    · linarith only [h2611, h2627, h2633, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2635 | h2635
                      · linarith only [h1367, h2613, h2629, h2635, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2637 | h2637
                        · linarith only [h1367, h2613, h2629, h2637, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h2144, h2637, hc45, hlam, hphi, ht34, u3ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2640 | h2640
            · linarith only [h2144, h2611, h2612, h2640, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2642 | h2642
              · linarith only [h2640, h2642, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2644 | h2644
                · linarith only [h2144, h2462, h2640, h2644, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2646 | h2646
                  · linarith only [h2611, h2612, h2646, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2648 | h2648
                    · linarith only [h2611, h2612, h2648, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h2611, h2612, h2648, hc35, hlam, hphi, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2651 | h2651
          · linarith only [h0, h1645, h2611, h2651, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2653 | h2653
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2654 | h2654
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2655 | h2655
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2656 | h2656
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2657 | h2657
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2658 | h2658
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2659 | h2659
                        · linarith only [h2144, h2462, h2659, hc34, hlam, hphi, u3ehi0]
                        · linarith only [h2144, h2611, h2653, h2655, h2659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h2144, h2611, h2653, h2655, h2656, h2658, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h2611, h2654, h2657, hlam]
                  · linarith only [h2611, h2654, h2656, hc34, hlam, hphi, u3ehi4]
                · linarith only [h2144, h2653, h2655, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h2144, h2653, h2654, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2667 | h2667
              · linarith only [h2653, h2667, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2669 | h2669
                · linarith only [h2144, h2462, h2653, h2669, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2671 | h2671
                  · linarith only [h0, h2611, h2653, h2671, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2611, h2671, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1367 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1500 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1645 | h1645
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x1_x0 m hb2 hb3 hb5 h0 h1367 h1500 h1645
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x1_x1 m hb2 hb3 hb5 h0 h1367 h1500 h1645

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1367 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1500 | h1500
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x0 m hb2 hb3 hb5 h0 h1367 h1500
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x1 m hb2 hb3 hb5 h0 h1367 h1500

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1367 | h1367
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1_x0 m hb2 hb3 hb5 h0 h1367
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1_x1 m hb2 hb3 hb5 h0 h1367

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0 m hb2 hb3 hb5 h0
  · exact r1l7_12_13_25_L_I_L_R_H_I_x1 m hb2 hb3 hb5 h0

end R2N4
