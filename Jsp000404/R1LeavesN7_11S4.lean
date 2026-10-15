import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2031 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h2032 | h2032
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2033 | h2033
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2034 | h2034
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2035 | h2035
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2036 | h2036
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2037 | h2037
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2038 | h2038
              · rcases h2bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  rcases p2039_3 (m.d 0 2) (by simp) with h2041 | h2041
                  · rcases p2039_3 (m.d 1 2) (by simp) with h2042 | h2042
                    · linarith only [h0, h2042, hlam]
                    · rcases p2039_3 (m.d 2 3) (by simp) with h2044 | h2044
                      · linarith only [h2044, h3, hlam]
                      · linarith only [h2044, h9, hlam]
                  · linarith only [h0, h2041, hlam]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h0, h2031, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  rcases p2039_3 (m.d 0 2) (by simp) with h2049 | h2049
                  · rcases p2039_3 (m.d 1 2) (by simp) with h2050 | h2050
                    · linarith only [h0, h2050, hlam]
                    · rcases p2039_3 (m.d 2 3) (by simp) with h2052 | h2052
                      · linarith only [h2052, h3, hlam]
                      · linarith only [h2035, h2052, hlam]
                  · linarith only [h2049, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h2031, h3, h9, hlam, p2039_2]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h0, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h9, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h3, h9, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h3, h9, hc02, hc25, hlam, hphi, ht0b, ht5b, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h3, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h0, h2031, h2036, h2038, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h0, h2035, h2038, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  rcases p2039_3 (m.d 0 2) (by simp) with h2066 | h2066
                  · rcases p2039_3 (m.d 1 2) (by simp) with h2067 | h2067
                    · linarith only [h2067, h9, hlam]
                    · linarith only [h2031, h2067, hlam]
                  · linarith only [h2066, h5, hlam]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h4, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h0, h2031, h2036, h2038, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h2035, hlam, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  rcases p2039_3 (m.d 0 2) (by simp) with h2075 | h2075
                  · rcases p2039_3 (m.d 1 2) (by simp) with h2076 | h2076
                    · linarith only [h0, h2036, h2038, h2076, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p2039_1]
                    · linarith only [h2031, h2076, hlam]
                  · linarith only [h2075, h5, hlam]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h5, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h2031, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h2036, hlam, p2039_1]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [h2037, hlam, p2039_0]
                · have p2039_0 := h2039c.1
                  have p2039_1 := h2039c.2.1
                  have p2039_2 := h2039c.2.2.1
                  have p2039_3 := h2039c.2.2.2
                  linarith only [hlam, p2039_0]
              · linarith only [h0, h2031, h2037, h2038, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2086 | h2086
              · linarith only [h2035, h2037, h2086, hlam]
              · rcases h2bigk with h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  rcases p2088_3 (m.d 0 2) (by simp) with h2090 | h2090
                  · rcases p2088_3 (m.d 1 2) (by simp) with h2091 | h2091
                    · linarith only [h0, h2091, hlam]
                    · rcases p2088_3 (m.d 2 3) (by simp) with h2093 | h2093
                      · linarith only [h2093, h3, hlam]
                      · linarith only [h2093, h9, hlam]
                  · linarith only [h0, h2090, hlam]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h0, h2031, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2032, h2034, h2037, h3, h9, hlam, p2088_2]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2031, h3, h9, hlam, p2088_2]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h0, hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h9, hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h0, h3, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h0, h3, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h3, hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h0, h2031, h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  rcases p2088_3 (m.d 0 2) (by simp) with h2108 | h2108
                  · rcases p2088_3 (m.d 1 2) (by simp) with h2109 | h2109
                    · linarith only [h2109, h9, hlam]
                    · linarith only [h2031, h2034, h2037, h2109, hlam]
                  · linarith only [h2108, h4, hlam]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  rcases p2088_3 (m.d 0 2) (by simp) with h2113 | h2113
                  · rcases p2088_3 (m.d 1 2) (by simp) with h2114 | h2114
                    · linarith only [h2114, h9, hlam]
                    · linarith only [h2031, h2114, hlam]
                  · linarith only [h2113, h5, hlam]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h4, hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2031, h2034, h2037, hlam, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2035, hlam, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2037, hlam, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h5, hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2031, hlam, p2088_0]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h2036, hlam, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [h0, h2031, h2035, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2088_1]
                · have p2088_0 := h2088c.1
                  have p2088_1 := h2088c.2.1
                  have p2088_2 := h2088c.2.2.1
                  have p2088_3 := h2088c.2.2.2
                  linarith only [hlam, p2088_0]
          · linarith only [h0, h2031, h2036, h3, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h2031, h2035, h3, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2130 | h2130
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2131 | h2131
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2132 | h2132
            · linarith only [h0, h2031, h2032, h2034, h2132, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2134 | h2134
              · linarith only [h2032, h2034, h2134, hlam]
              · rcases h2bigk with h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  rcases p2136_3 (m.d 0 2) (by simp) with h2138 | h2138
                  · rcases p2136_3 (m.d 1 2) (by simp) with h2139 | h2139
                    · linarith only [h0, h2139, hlam]
                    · rcases p2136_3 (m.d 2 3) (by simp) with h2141 | h2141
                      · linarith only [h2141, h3, hlam]
                      · linarith only [h2141, h9, hlam]
                  · linarith only [h0, h2138, hlam]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h0, h2031, h2132, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2031, h2132, h3, h9, hlam, p2136_2]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2031, h3, h9, hlam, p2136_2]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h0, hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h9, hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h0, h2130, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h0, h3, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h3, hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h0, h2031, h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  rcases p2136_3 (m.d 0 2) (by simp) with h2156 | h2156
                  · rcases p2136_3 (m.d 1 2) (by simp) with h2157 | h2157
                    · linarith only [h2157, h9, hlam]
                    · linarith only [h0, h2031, h2131, h2134, h2157, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2136_1]
                  · linarith only [h2156, h4, hlam]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  rcases p2136_3 (m.d 0 2) (by simp) with h2161 | h2161
                  · rcases p2136_3 (m.d 1 2) (by simp) with h2162 | h2162
                    · linarith only [h2162, h9, hlam]
                    · linarith only [h2031, h2162, hlam]
                  · linarith only [h2161, h5, hlam]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h4, hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2031, h2132, hlam, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2130, hlam, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2132, hlam, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h5, hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2031, hlam, p2136_0]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h2131, hlam, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [h0, h2031, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2136_1]
                · have p2136_0 := h2136c.1
                  have p2136_1 := h2136c.2.1
                  have p2136_2 := h2136c.2.2.1
                  have p2136_3 := h2136c.2.2.2
                  linarith only [hlam, p2136_0]
          · linarith only [h0, h2031, h2131, h3, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h2031, h2130, h3, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
    · linarith only [h2031, h2033, h9, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2179 | h2179
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2180 | h2180
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2181 | h2181
        · linarith only [h0, h2032, h2179, h2181, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h2031, h2181, h3, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h2031, h2032, h2180, h9, hlam]
    · linarith only [h2031, h2179, h9, hlam]

end R2N4
