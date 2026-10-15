import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S2
import Jsp000404.R1LeavesN7_17S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9

set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h2024 | h2024
  · linarith only [h2024, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2026 | h2026
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2027 | h2027
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2028 | h2028
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2029 | h2029
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2030 | h2030
            · linarith only [h2, h2024, h2030, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2032 | h2032
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2033 | h2033
                · linarith only [h0, h2026, h2033, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2035 | h2035
                  · linarith only [h2, h2024, h2027, h2035, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2037 | h2037
                    · linarith only [h1, h2, h2024, h2026, h2027, h2032, h2037, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases h0bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h0, h2028, h2033, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2043 | h2043
                        · rcases p2039_3 (m.d 0 2) (by simp) with h2044 | h2044
                          · linarith only [h0, h2044, hlam]
                          · linarith only [h2044, h5, hlam]
                        · linarith only [h2, h2043, hlam]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h1, h2026, h2032, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2039_1]
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
                        linarith only [h1, h2026, h2032, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2052 | h2052
                        · rcases p2039_3 (m.d 0 2) (by simp) with h2053 | h2053
                          · rcases p2039_3 (m.d 0 3) (by simp) with h2054 | h2054
                            · linarith only [h2054, h4, hlam]
                            · linarith only [h2054, h7, hlam]
                          · linarith only [h2053, h5, hlam]
                        · linarith only [h2, h2052, hlam]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h0, h1, h2026, h2032, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h1, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h4, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2, h2027, h2032, h2037, h8, hc34, hc45, hlam, hphi, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h8, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h5, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h7, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2024, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h3, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h6, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h1, h2026, h2032, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2, h2027, h2032, h2037, h8, hc34, hc45, hlam, hphi, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
              · linarith only [h2032, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h2029, h7, h8, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2077 | h2077
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2078 | h2078
            · linarith only [h2, h2024, h2078, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2080 | h2080
              · linarith only [h2024, h2026, h2028, h2080, h6, hc34, hc45, hlam, hphi]
              · linarith only [h2080, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h2077, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h2026, h2027, h5, h7, h8, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2085 | h2085
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2086 | h2086
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2087 | h2087
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2088 | h2088
            · linarith only [h2, h2024, h2088, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2090 | h2090
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2091 | h2091
                · linarith only [h2091, h4, h8, hlam]
                · linarith only [h2026, h2086, h2091, hlam]
              · linarith only [h2026, h2085, h2090, h7, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h2026, h2085, h2087, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2096 | h2096
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2097 | h2097
            · linarith only [h2, h2024, h2097, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2099 | h2099
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2100 | h2100
                · linarith only [h2100, h4, h8, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2102 | h2102
                  · linarith only [h2024, h2026, h2085, h2102, h4, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2104 | h2104
                    · linarith only [h2024, h2026, h2085, h2099, h2104, h4, h8, hlam]
                    · linarith only [h2026, h2085, h2099, h2104, h4, h8, hc34, hc45, hlam, hphi]
              · linarith only [h2026, h2085, h2099, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h2096, h7, h8, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2109 | h2109
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2110 | h2110
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2111 | h2111
            · linarith only [h2024, h2085, h2109, h2111, h5, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h2085, h2109, h2111, hlam]
          · linarith only [h2026, h2110, h7, h8, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2115 | h2115
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2116 | h2116
            · linarith only [h2, h2024, h2116, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2118 | h2118
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2119 | h2119
                · linarith only [h2119, h4, h8, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2121 | h2121
                  · linarith only [h2024, h2121, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2123 | h2123
                    · linarith only [h2024, h2085, h2115, h2123, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h0bigk with h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2085, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2085, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h0, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2085, h5, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h0, h2085, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h0, h2085, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h1, hlam, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h4, hlam, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2085, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h8, hlam, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h5, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h7, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2024, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h3, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h6, hlam, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h0, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2085, h2123, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
              · linarith only [h2026, h2118, h7, h8, hc13, hc35, hlam, hphi]
          · linarith only [h2026, h2115, h7, h8, hc12, hc35, hlam, hphi, ht23]

set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8
  · exact r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8

set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2153 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h2154 | h2154
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2155 | h2155
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2156 | h2156
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2157 | h2157
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2158 | h2158
          · linarith only [h1, h2153, h2158, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2160 | h2160
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2161 | h2161
              · linarith only [h1, h2155, h2161, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2163 | h2163
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2164 | h2164
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2165 | h2165
                    · rcases h0bigk with h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h2163, h2165, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h1, h2155, h2163, h2165, hc01, hc45, hlam, hphi, ht0b, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h1, h2155, h2163, h2165, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        rcases p2166_3 (m.d 0 1) (by simp) with h2171 | h2171
                        · rcases p2166_3 (m.d 0 2) (by simp) with h2172 | h2172
                          · linarith only [h0, h2172, hlam]
                          · linarith only [h2172, h6, hlam]
                        · linarith only [h2171, h3, hlam]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h0, hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h1, h2155, h2163, h2165, hc02, hc45, hlam, hphi, ht0b, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h0, h1, h2155, h2163, h2165, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        rcases p2166_3 (m.d 0 1) (by simp) with h2180 | h2180
                        · rcases p2166_3 (m.d 0 2) (by simp) with h2181 | h2181
                          · rcases p2166_3 (m.d 0 3) (by simp) with h2182 | h2182
                            · linarith only [h2182, h4, hlam]
                            · linarith only [h2153, h2182, hlam]
                          · linarith only [h2181, h6, hlam]
                        · linarith only [h2180, h3, hlam]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h1, hlam, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h4, hlam, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h7, hlam, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h2, hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h5, hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h1, h2155, h2163, h2165, hc04, hc45, hlam, hphi, ht0b, ht5b, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        rcases p2166_3 (m.d 0 1) (by simp) with h2196 | h2196
                        · rcases p2166_3 (m.d 0 2) (by simp) with h2197 | h2197
                          · rcases p2166_3 (m.d 0 3) (by simp) with h2198 | h2198
                            · linarith only [h2198, h7, hlam]
                            · linarith only [h2153, h2198, hlam]
                          · linarith only [h2197, h6, hlam]
                        · linarith only [h2196, h3, hlam]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h3, hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h6, hlam, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h2153, hlam, p2166_0]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [h2154, hlam, p2166_1]
                      · have p2166_0 := h2166c.1
                        have p2166_1 := h2166c.2.1
                        have p2166_2 := h2166c.2.2.1
                        have p2166_3 := h2166c.2.2.2
                        linarith only [hlam, p2166_0]
                    · linarith only [h1, h2154, h2155, h2163, h2165, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2156, h2160, h2161, h2163, h2164, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h2153, h2163, h7, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2211 | h2211
              · linarith only [h0, h2153, h2154, h2160, h2211, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2213 | h2213
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2214 | h2214
                  · linarith only [h0, h2155, h2158, h2160, h2213, h2214, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2211, h2213, h2214, hlam]
                · linarith only [h2153, h2213, h7, hc23, hc34, hlam, hphi]
        · linarith only [h2153, h2155, h2157, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2219 | h2219
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2220 | h2220
          · linarith only [h1, h2153, h2220, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2222 | h2222
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2223 | h2223
              · linarith only [h2155, h2156, h2223, h5, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2225 | h2225
                · linarith only [h0, h2155, h2156, h2225, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h2153, h2225, h7, hc23, hc34, hlam, hphi]
            · linarith only [h2153, h2154, h2155, h2156, h2222, h7, hc23, hc34, hlam, hphi]
        · linarith only [h2153, h2155, h2219, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2230 | h2230
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2231 | h2231
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2232 | h2232
          · linarith only [h2155, h2230, h2232, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h2155, h2230, h2232, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2235 | h2235
          · linarith only [h2153, h2230, h2231, h2235, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h2155, h2230, h2235, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2238 | h2238
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2239 | h2239
          · linarith only [h1, h2153, h2239, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2241 | h2241
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2242 | h2242
              · linarith only [h2242, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2244 | h2244
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2245 | h2245
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2246 | h2246
                    · rcases h0bigk with h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h0, h2238, h2244, h2246, hc01, hc45, hlam, hphi, ht0b, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2155, h2238, h2244, h2246, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2155, h2238, h2244, h2246, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        rcases p2247_3 (m.d 0 1) (by simp) with h2252 | h2252
                        · rcases p2247_3 (m.d 0 2) (by simp) with h2253 | h2253
                          · linarith only [h0, h2253, hlam]
                          · linarith only [h2253, h6, hlam]
                        · linarith only [h2252, h3, hlam]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h0, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2155, h2238, h2244, h2246, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h0, h2155, h2238, h2244, h2246, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        rcases p2247_3 (m.d 0 1) (by simp) with h2261 | h2261
                        · rcases p2247_3 (m.d 0 2) (by simp) with h2262 | h2262
                          · rcases p2247_3 (m.d 0 3) (by simp) with h2263 | h2263
                            · linarith only [h2263, h4, hlam]
                            · linarith only [h2153, h2263, hlam]
                          · linarith only [h2262, h6, hlam]
                        · linarith only [h2261, h3, hlam]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h1, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h4, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h7, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h5, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2155, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        rcases p2247_3 (m.d 0 1) (by simp) with h2277 | h2277
                        · rcases p2247_3 (m.d 0 2) (by simp) with h2278 | h2278
                          · rcases p2247_3 (m.d 0 3) (by simp) with h2279 | h2279
                            · linarith only [h2279, h7, hlam]
                            · linarith only [h2153, h2279, hlam]
                          · linarith only [h2278, h6, hlam]
                        · linarith only [h2277, h3, hlam]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h3, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h6, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2153, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2154, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                    · linarith only [h2155, h2246, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2155, h2238, h2241, h2242, h2244, h2245, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h2153, h2155, h2238, h2244, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h2155, h2238, h2239, h2241, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2293 | h2293
          · linarith only [h1, h2153, h2293, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2295 | h2295
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2296 | h2296
              · linarith only [h2296, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2298 | h2298
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2299 | h2299
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2300 | h2300
                    · rcases h0bigk with h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c | h2301c
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2230, h2293, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2153, h2238, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2153, h2238, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2238, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h0, hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2153, h2238, h6, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h0, h2153, h2238, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h0, h2238, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h1, hlam, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h4, hlam, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h7, hlam, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2238, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2, hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h5, hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2298, h4, hc04, hc35, hlam, hphi, ht0b, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2238, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h3, hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h6, hlam, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2153, hlam, p2301_0]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [h2154, hlam, p2301_1]
                      · have p2301_0 := h2301c.1
                        have p2301_1 := h2301c.2.1
                        have p2301_2 := h2301c.2.2.1
                        have p2301_3 := h2301c.2.2.2
                        linarith only [hlam, p2301_0]
                    · linarith only [h2, h2295, h2300, h7, hlam]
                  · linarith only [h2153, h2230, h2238, h2295, h2299, h6, h7, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2153, h2155, h2298, h7, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2330 | h2330
              · linarith only [h0, h2153, h2154, h2295, h2330, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2332 | h2332
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2333 | h2333
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2334 | h2334
                    · linarith only [h2155, h2293, h2295, h2332, h2334, h4, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h2333, h2334, h5, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2153, h2154, h2230, h2333, h7, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2153, h2332, h7, hc23, hc34, hlam, hphi]
  · linarith only [h2153, h2154, h7, hlam]

set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2153 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h2340 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h2341 | h2341
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2342 | h2342
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2343 | h2343
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2344 | h2344
        · linarith only [h1, h2344, h7, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2346 | h2346
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2347 | h2347
            · linarith only [h2347, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2349 | h2349
              · linarith only [h0, h2153, h2342, h2347, h2349, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2351 | h2351
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2352 | h2352
                  · rcases h0bigk with h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c | h2353c
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      rcases p2353_3 (m.d 0 1) (by simp) with h2356 | h2356
                      · rcases p2353_3 (m.d 0 2) (by simp) with h2357 | h2357
                        · linarith only [h0, h2357, hlam]
                        · linarith only [h2357, h4, hlam]
                      · linarith only [h1, h2356, hlam]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h2, h2342, h2351, hc01, hc45, hlam, hphi, ht0b, ht5b, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      rcases p2353_3 (m.d 0 1) (by simp) with h2362 | h2362
                      · rcases p2353_3 (m.d 0 2) (by simp) with h2363 | h2363
                        · linarith only [h0, h2363, hlam]
                        · linarith only [h2363, h6, hlam]
                      · linarith only [h2362, h3, hlam]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h0, hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      rcases p2353_3 (m.d 0 1) (by simp) with h2369 | h2369
                      · rcases p2353_3 (m.d 0 2) (by simp) with h2370 | h2370
                        · rcases p2353_3 (m.d 0 3) (by simp) with h2371 | h2371
                          · linarith only [h2371, h4, hlam]
                          · rcases p2353_3 (m.d 0 4) (by simp) with h2373 | h2373
                            · linarith only [h2373, h5, hlam]
                            · linarith only [h2373, h7, hlam]
                        · linarith only [h2370, h4, hlam]
                      · linarith only [h1, h2369, hlam]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h2, h2342, h2351, hc02, hc45, hlam, hphi, ht0b, ht5b, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      rcases p2353_3 (m.d 0 1) (by simp) with h2379 | h2379
                      · rcases p2353_3 (m.d 0 2) (by simp) with h2380 | h2380
                        · rcases p2353_3 (m.d 0 3) (by simp) with h2381 | h2381
                          · linarith only [h2381, h4, hlam]
                          · rcases p2353_3 (m.d 0 4) (by simp) with h2383 | h2383
                            · linarith only [h2383, h5, hlam]
                            · linarith only [h2340, h2383, hlam]
                        · linarith only [h2380, h6, hlam]
                      · linarith only [h2379, h3, hlam]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h1, hlam, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h4, hlam, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h7, hlam, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h2153, hlam, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h2, hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h5, hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h1, h2341, h7, hc23, hc34, hlam, hphi, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h1, h2153, h2341, h7, hc23, hc34, hlam, hphi, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h3, hlam, p2353_0]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h6, hlam, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h1, h2153, h2341, hc23, hc35, hlam, hphi, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [h2340, hlam, p2353_1]
                    · have p2353_0 := h2353c.1
                      have p2353_1 := h2353c.2.1
                      have p2353_2 := h2353c.2.2.1
                      have p2353_3 := h2353c.2.2.2
                      linarith only [hlam, p2353_0]
                  · linarith only [h0, h2342, h2351, h2352, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2404 | h2404
                  · rcases h0bigk with h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c | h2405c
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      rcases p2405_3 (m.d 0 1) (by simp) with h2408 | h2408
                      · rcases p2405_3 (m.d 0 2) (by simp) with h2409 | h2409
                        · linarith only [h0, h2409, hlam]
                        · linarith only [h2409, h4, hlam]
                      · linarith only [h1, h2408, hlam]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2, h2346, h2347, h2351, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2346, h2347, h2351, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h0, hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      rcases p2405_3 (m.d 0 1) (by simp) with h2417 | h2417
                      · rcases p2405_3 (m.d 0 2) (by simp) with h2418 | h2418
                        · rcases p2405_3 (m.d 0 3) (by simp) with h2419 | h2419
                          · linarith only [h2419, h4, hlam]
                          · rcases p2405_3 (m.d 0 4) (by simp) with h2421 | h2421
                            · linarith only [h2421, h5, hlam]
                            · linarith only [h2421, h7, hlam]
                        · linarith only [h2418, h4, hlam]
                      · linarith only [h1, h2417, hlam]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2, h2346, h2347, h2351, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h0, h2346, h2347, h2351, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h1, hlam, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h4, hlam, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h7, hlam, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2153, hlam, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2, hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h5, hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h1, h2341, h7, hc23, hc34, hlam, hphi, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2346, h2347, h2351, h3, h7, hc23, hc34, hlam, hphi, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h3, hlam, p2405_0]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h6, hlam, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h1, h2153, h2341, h2404, hc23, hc34, hlam, hphi, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [h2340, hlam, p2405_1]
                    · have p2405_0 := h2405c.1
                      have p2405_1 := h2405c.2.1
                      have p2405_2 := h2405c.2.2.1
                      have p2405_3 := h2405c.2.2.2
                      linarith only [hlam, p2405_0]
                  · linarith only [h2, h2346, h2404, h7, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2444 | h2444
            · linarith only [h2340, h2341, h2344, h2346, h2444, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2446 | h2446
              · linarith only [h1, h2153, h2341, h2446, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2448 | h2448
                · linarith only [h0, h2341, h2342, h2344, h2346, h2448, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2450 | h2450
                  · rcases h0bigk with h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      rcases p2451_3 (m.d 0 1) (by simp) with h2454 | h2454
                      · rcases p2451_3 (m.d 0 2) (by simp) with h2455 | h2455
                        · linarith only [h0, h2455, hlam]
                        · linarith only [h2455, h4, hlam]
                      · linarith only [h1, h2454, hlam]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2340, h2341, h2344, h2346, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2340, h2341, h2344, h2346, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h0, hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      rcases p2451_3 (m.d 0 1) (by simp) with h2463 | h2463
                      · rcases p2451_3 (m.d 0 2) (by simp) with h2464 | h2464
                        · rcases p2451_3 (m.d 0 3) (by simp) with h2465 | h2465
                          · linarith only [h2465, h4, hlam]
                          · rcases p2451_3 (m.d 0 4) (by simp) with h2467 | h2467
                            · linarith only [h2467, h5, hlam]
                            · linarith only [h2467, h7, hlam]
                        · linarith only [h2464, h4, hlam]
                      · linarith only [h1, h2463, hlam]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2340, h2341, h2344, h2346, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h0, h2340, h2341, h2344, h2346, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h1, hlam, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h4, hlam, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h7, hlam, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2153, hlam, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2, hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h5, hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h1, h2341, h7, hc23, hc34, hlam, hphi, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2340, h2341, h2344, h2346, h7, hc23, hc34, hlam, hphi, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h3, hlam, p2451_0]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h6, hlam, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h1, h2153, h2341, hc23, hc35, hlam, hphi, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [h2340, hlam, p2451_1]
                    · have p2451_0 := h2451c.1
                      have p2451_1 := h2451c.2.1
                      have p2451_2 := h2451c.2.2.1
                      have p2451_3 := h2451c.2.2.2
                      linarith only [hlam, p2451_0]
                  · linarith only [h2340, h2450, h7, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2490 | h2490
        · linarith only [h1, h2340, h2341, h2343, h2490, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2492 | h2492
          · linarith only [h2342, h2343, h2492, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2494 | h2494
            · linarith only [h2341, h2343, h2494, h6, h7, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2496 | h2496
              · linarith only [h1, h2153, h2341, h2496, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2498 | h2498
                · linarith only [h0, h2342, h2343, h2490, h2492, h2498, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h2340, h2341, h2343, h2498, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2501 | h2501
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2502 | h2502
        · linarith only [h1, h2, h2153, h2341, h2342, h2502, h7, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2504 | h2504
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2505 | h2505
            · linarith only [h0, h2341, h2342, h2505, h5, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2507 | h2507
              · linarith only [h1, h2153, h2341, h2507, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2509 | h2509
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2510 | h2510
                  · rcases h0bigk with h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2342, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 1) (by simp) with h2514 | h2514
                      · rcases p2511_3 (m.d 0 2) (by simp) with h2515 | h2515
                        · linarith only [h0, h2515, hlam]
                        · linarith only [h2515, h4, hlam]
                      · linarith only [h1, h2514, hlam]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2342, h2501, h2507, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 1) (by simp) with h2520 | h2520
                      · rcases p2511_3 (m.d 0 2) (by simp) with h2521 | h2521
                        · linarith only [h0, h2521, hlam]
                        · linarith only [h2521, h6, hlam]
                      · linarith only [h2520, h3, hlam]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 1) (by simp) with h2527 | h2527
                      · rcases p2511_3 (m.d 0 2) (by simp) with h2528 | h2528
                        · rcases p2511_3 (m.d 0 3) (by simp) with h2529 | h2529
                          · linarith only [h2529, h4, hlam]
                          · rcases p2511_3 (m.d 0 4) (by simp) with h2531 | h2531
                            · linarith only [h2531, h5, hlam]
                            · linarith only [h2531, h7, hlam]
                        · linarith only [h2528, h4, hlam]
                      · linarith only [h1, h2527, hlam]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2342, h2501, h2507, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      rcases p2511_3 (m.d 0 1) (by simp) with h2537 | h2537
                      · rcases p2511_3 (m.d 0 2) (by simp) with h2538 | h2538
                        · rcases p2511_3 (m.d 0 3) (by simp) with h2539 | h2539
                          · linarith only [h2539, h4, hlam]
                          · rcases p2511_3 (m.d 0 4) (by simp) with h2541 | h2541
                            · linarith only [h2541, h5, hlam]
                            · linarith only [h2340, h2541, hlam]
                        · linarith only [h2538, h6, hlam]
                      · linarith only [h2537, h3, hlam]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h1, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h4, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h7, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2153, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h5, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h1, h2341, h7, hc23, hc34, hlam, hphi, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h1, h2153, h2341, h7, hc23, hc34, hlam, hphi, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h3, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h6, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h1, h2153, h2341, hc23, hc35, hlam, hphi, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2340, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                  · linarith only [h2, h2342, h2501, h2509, h2510, h7, hlam]
                · linarith only [h2342, h2501, h2507, h2509, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2340, h2341, h2342, h2504, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2564 | h2564
        · linarith only [h1, h2340, h2341, h2501, h2564, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2566 | h2566
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2567 | h2567
            · linarith only [h2340, h2341, h2501, h2567, h6, h7, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2569 | h2569
              · linarith only [h1, h2153, h2341, h2569, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2571 | h2571
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2572 | h2572
                  · rcases h0bigk with h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2501, h2571, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      rcases p2573_3 (m.d 0 1) (by simp) with h2576 | h2576
                      · rcases p2573_3 (m.d 0 2) (by simp) with h2577 | h2577
                        · linarith only [h0, h2577, hlam]
                        · linarith only [h2577, h4, hlam]
                      · linarith only [h1, h2576, hlam]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2, h2341, h2501, h2566, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2341, h2501, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h0, hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      rcases p2573_3 (m.d 0 1) (by simp) with h2585 | h2585
                      · rcases p2573_3 (m.d 0 2) (by simp) with h2586 | h2586
                        · rcases p2573_3 (m.d 0 3) (by simp) with h2587 | h2587
                          · linarith only [h2587, h4, hlam]
                          · rcases p2573_3 (m.d 0 4) (by simp) with h2589 | h2589
                            · linarith only [h2589, h5, hlam]
                            · linarith only [h2589, h7, hlam]
                        · linarith only [h2586, h4, hlam]
                      · linarith only [h1, h2585, hlam]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h0, h2341, h2501, h2571, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h0, h2341, h2501, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h1, hlam, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h4, hlam, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h7, hlam, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2153, hlam, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2, hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h5, hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h7, hc03, hc34, hlam, hphi, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2341, h2501, h6, h7, hc23, hc34, hlam, hphi, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h3, hlam, p2573_0]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h6, hlam, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h1, h2153, hc13, hc35, hlam, hphi, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [h2340, hlam, p2573_1]
                    · have p2573_0 := h2573c.1
                      have p2573_1 := h2573c.2.1
                      have p2573_2 := h2573c.2.2.1
                      have p2573_3 := h2573c.2.2.2
                      linarith only [hlam, p2573_0]
                  · linarith only [h2, h2566, h2572, h7, hlam]
                · linarith only [h2340, h2341, h2342, h2571, h7, hc23, hc34, hlam, hphi]
          · linarith only [h2340, h2341, h2342, h2566, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2614 | h2614
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2615 | h2615
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2616 | h2616
        · linarith only [h2341, h2614, h2616, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
        · linarith only [h2341, h2614, h2616, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2619 | h2619
        · linarith only [h2341, h2614, h2619, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
        · linarith only [h2341, h2614, h2619, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2622 | h2622
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2623 | h2623
        · linarith only [h2341, h2622, h2623, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2625 | h2625
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2626 | h2626
            · linarith only [h2626, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2628 | h2628
              · linarith only [h2153, h2628, h4, hlam]
              · linarith only [h2341, h2622, h2628, hlam]
          · linarith only [h2341, h2622, h2623, h2625, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2632 | h2632
        · linarith only [h1, h2153, h2614, h2632, h5, h7, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2634 | h2634
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2635 | h2635
            · linarith only [h2635, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2637 | h2637
              · linarith only [h2153, h2637, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2639 | h2639
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2640 | h2640
                  · rcases h0bigk with h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2637, h2639, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2341, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2, h2634, hc01, hc45, hlam, hphi, ht0b, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2153, h2341, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h0, hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2341, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h0, h2, h2634, hc01, hc45, hlam, hphi, ht0b, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h0, h2153, h2341, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h1, hlam, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h4, hlam, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h7, hlam, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2153, hlam, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2, hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h5, hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2341, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2153, h2341, h4, h7, hc12, hc34, hlam, hphi, ht23, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h3, hlam, p2641_0]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h6, hlam, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2341, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [h2340, hlam, p2641_1]
                    · have p2641_0 := h2641c.1
                      have p2641_1 := h2641c.2.1
                      have p2641_2 := h2641c.2.2.1
                      have p2641_3 := h2641c.2.2.2
                      linarith only [hlam, p2641_0]
                  · linarith only [h2, h2634, h2640, h7, hlam]
                · linarith only [h2614, h2634, h2639, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2669 | h2669
            · linarith only [h2340, h2341, h2632, h2634, h2669, h7, hc12, hc23, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2671 | h2671
              · linarith only [h2153, h2671, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2673 | h2673
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2674 | h2674
                  · rcases h0bigk with h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c | h2675c
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h2632, h2634, h2673, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h2671, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h0, hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h0, h2341, h2632, h2634, h2673, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h0, h2341, h2671, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h1, hlam, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h4, hlam, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h7, hlam, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2153, hlam, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2, hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h5, hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h2671, h6, h7, hc12, hc34, hlam, hphi, ht23, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h3, hlam, p2675_0]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h6, hlam, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2341, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [h2340, hlam, p2675_1]
                    · have p2675_0 := h2675c.1
                      have p2675_1 := h2675c.2.1
                      have p2675_2 := h2675c.2.2.1
                      have p2675_3 := h2675c.2.2.2
                      linarith only [hlam, p2675_0]
                  · linarith only [h2673, h2674, h5, h7, hlam]
                · linarith only [h2340, h2614, h2673, h7, hc12, hc34, hlam, hphi, ht23]

end R2N4
