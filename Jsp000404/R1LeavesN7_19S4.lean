import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h2049 | h2049
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2050 | h2050
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2051 | h2051
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2052 | h2052
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2053 | h2053
          · linarith only [h1, h2053, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2055 | h2055
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2056 | h2056
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2057 | h2057
                · linarith only [h0, h2, h2050, h2053, h2055, h2057, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2059 | h2059
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2060 | h2060
                    · rcases h1bigk with h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2051, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2055, h2060, hc01, hc45, hlam, hphi, ht0b, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2053, h2055, h2060, hc01, hc45, hlam, hphi, ht0b, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        rcases p2061_3 (m.d 0 1) (by simp) with h2066 | h2066
                        · rcases p2061_3 (m.d 1 2) (by simp) with h2067 | h2067
                          · linarith only [h0, h2067, hlam]
                          · linarith only [h2052, h2067, hlam]
                        · linarith only [h2066, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h0, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2055, h2060, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h0, h2053, h2055, h2060, hc01, hc45, hlam, hphi, ht0b, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h1, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2050, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2053, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h1, h2052, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2051, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h0, h2051, h2055, h2060, hc01, hc45, hlam, hphi, ht0b, ht5b, p2061_1]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h3, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2052, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2055, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [h2056, hlam, p2061_0]
                      · have p2061_0 := h2061c.1
                        have p2061_1 := h2061c.2.1
                        have p2061_2 := h2061c.2.2.1
                        have p2061_3 := h2061c.2.2.2
                        linarith only [hlam, p2061_0]
                    · linarith only [h1, h2055, h2059, h2060, h5, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2092 | h2092
                    · linarith only [h1, h2055, h2057, h2059, h2092, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h1, h2, h2055, h2056, h2092, h5, hc04, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h2053, h2055, h2056, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2096 | h2096
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2097 | h2097
                · linarith only [h0, h2, h2050, h2096, h2097, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2100 | h2100
                    · rcases h1bigk with h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c | h2101c
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2051, h2097, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        rcases p2101_3 (m.d 0 1) (by simp) with h2104 | h2104
                        · rcases p2101_3 (m.d 1 2) (by simp) with h2105 | h2105
                          · linarith only [h0, h2105, hlam]
                          · linarith only [h2050, h2105, hlam]
                        · linarith only [h2104, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2051, h2099, hc01, hc45, hlam, hphi, ht0b, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        rcases p2101_3 (m.d 0 1) (by simp) with h2110 | h2110
                        · rcases p2101_3 (m.d 1 2) (by simp) with h2111 | h2111
                          · linarith only [h0, h2111, hlam]
                          · linarith only [h2052, h2111, hlam]
                        · linarith only [h2110, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h0, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h0, h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h0, h2051, h2099, hc01, hc45, hlam, hphi, ht0b, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h0, h2050, h2055, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h1, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2050, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2053, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2055, hlam, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2051, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2, h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h0, h2050, h2051, h2055, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h3, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2052, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2050, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2101_1]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [h2096, hlam, p2101_0]
                      · have p2101_0 := h2101c.1
                        have p2101_1 := h2101c.2.1
                        have p2101_2 := h2101c.2.2.1
                        have p2101_3 := h2101c.2.2.2
                        linarith only [hlam, p2101_0]
                    · linarith only [h2099, h2100, h4, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2136 | h2136
                    · rcases h1bigk with h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c | h2137c
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        rcases p2137_3 (m.d 0 1) (by simp) with h2140 | h2140
                        · rcases p2137_3 (m.d 1 2) (by simp) with h2141 | h2141
                          · linarith only [h0, h2141, hlam]
                          · linarith only [h2050, h2141, hlam]
                        · linarith only [h2140, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2096, h2097, h2099, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2096, h2097, h2099, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h0, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h0, h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h0, h2096, h2097, h2099, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h1, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2050, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2053, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2055, hlam, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2051, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2, h2050, h5, hc23, hc34, hlam, hphi, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h0, h2050, h2051, h2055, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h3, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2052, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2050, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2137_1]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [h2096, hlam, p2137_0]
                      · have p2137_0 := h2137c.1
                        have p2137_1 := h2137c.2.1
                        have p2137_2 := h2137c.2.2.1
                        have p2137_3 := h2137c.2.2.2
                        linarith only [hlam, p2137_0]
                    · linarith only [h2049, h2136, h5, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2168 | h2168
                · linarith only [h1, h2049, h2050, h2096, h2168, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2170 | h2170
                  · linarith only [h0, h2050, h2051, h2053, h2096, h2170, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2172 | h2172
                    · rcases h1bigk with h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        rcases p2173_3 (m.d 0 1) (by simp) with h2176 | h2176
                        · rcases p2173_3 (m.d 1 2) (by simp) with h2177 | h2177
                          · linarith only [h0, h2177, hlam]
                          · linarith only [h2050, h2177, hlam]
                        · linarith only [h2176, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        rcases p2173_3 (m.d 0 1) (by simp) with h2181 | h2181
                        · rcases p2173_3 (m.d 1 2) (by simp) with h2182 | h2182
                          · linarith only [h0, h2182, hlam]
                          · linarith only [h2051, h2182, hlam]
                        · linarith only [h2181, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        rcases p2173_3 (m.d 0 1) (by simp) with h2186 | h2186
                        · rcases p2173_3 (m.d 1 2) (by simp) with h2187 | h2187
                          · linarith only [h0, h2187, hlam]
                          · linarith only [h2052, h2187, hlam]
                        · linarith only [h2186, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h0, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h0, h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h0, h2050, h2053, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h1, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2050, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2053, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2055, hlam, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2051, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2049, h2050, h2096, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2096, hlam, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h3, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2052, hlam, p2173_0]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2050, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [h2049, h2096, h5, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2173_1]
                      · have p2173_0 := h2173c.1
                        have p2173_1 := h2173c.2.1
                        have p2173_2 := h2173c.2.2.1
                        have p2173_3 := h2173c.2.2.2
                        linarith only [hlam, p2173_0]
                    · linarith only [h2049, h2172, h5, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2212 | h2212
          · linarith only [h1, h2212, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2214 | h2214
            · linarith only [h2050, h2052, h2214, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2216 | h2216
              · linarith only [h2051, h2052, h2216, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2218 | h2218
                · linarith only [h2049, h2050, h2212, h2216, h2218, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2220 | h2220
                  · linarith only [h2051, h2052, h2216, h2220, hlam]
                  · linarith only [h2049, h2051, h2052, h2218, h2220, h5, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2223 | h2223
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2224 | h2224
          · linarith only [h1, h2051, h2223, h2224, h4, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2226 | h2226
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2227 | h2227
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2228 | h2228
                · linarith only [h2050, h2051, h2228, h4, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2230 | h2230
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2231 | h2231
                    · rcases h1bigk with h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2226, hc01, hc35, hlam, hphi, ht0b, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2050, h2051, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        rcases p2232_3 (m.d 0 1) (by simp) with h2237 | h2237
                        · rcases p2232_3 (m.d 1 2) (by simp) with h2238 | h2238
                          · linarith only [h0, h2238, hlam]
                          · linarith only [h2223, h2238, hlam]
                        · linarith only [h2237, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2051, h2226, h2231, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2051, hlam, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h2051, h2223, h2230, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h1, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2050, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2224, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h1, h2223, h2230, hc01, hc45, hlam, hphi, ht0b, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2050, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h2051, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h2051, h2223, h2230, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h3, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2223, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2226, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2227, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                    · linarith only [h2049, h2231, h5, hlam]
                  · linarith only [h2050, h2051, h2230, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2049, h2050, h2051, h2227, h5, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2265 | h2265
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2266 | h2266
                · linarith only [h0, h2050, h2266, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2268 | h2268
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2269 | h2269
                    · rcases h1bigk with h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c | h2270c
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2223, hc01, hc25, hlam, hphi, ht0b, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        rcases p2270_3 (m.d 0 1) (by simp) with h2273 | h2273
                        · rcases p2270_3 (m.d 1 2) (by simp) with h2274 | h2274
                          · linarith only [h0, h2274, hlam]
                          · linarith only [h2050, h2274, hlam]
                        · linarith only [h2273, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2050, h2051, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        rcases p2270_3 (m.d 0 1) (by simp) with h2279 | h2279
                        · rcases p2270_3 (m.d 1 2) (by simp) with h2280 | h2280
                          · linarith only [h0, h2280, hlam]
                          · linarith only [h2223, h2280, hlam]
                        · linarith only [h2279, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h0, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h0, h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2051, hlam, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h0, h2051, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h1, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2050, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2224, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2226, hlam, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h0, h2051, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h0, h2050, h2051, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h0, h2050, h2051, h2226, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h3, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2223, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2050, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2270_1]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [h2265, hlam, p2270_0]
                      · have p2270_0 := h2270c.1
                        have p2270_1 := h2270c.2.1
                        have p2270_2 := h2270c.2.2.1
                        have p2270_3 := h2270c.2.2.2
                        linarith only [hlam, p2270_0]
                    · linarith only [h2049, h2269, h5, hlam]
                  · linarith only [h2051, h2223, h2265, h2268, hlam]
              · linarith only [h2049, h2050, h2051, h2265, h5, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2307 | h2307
          · linarith only [h1, h2050, h2051, h2307, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2309 | h2309
            · linarith only [h2050, h2223, h2309, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2311 | h2311
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2312 | h2312
                · linarith only [h2050, h2051, h2312, h4, h5, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2314 | h2314
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2315 | h2315
                    · rcases h1bigk with h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        rcases p2316_3 (m.d 0 1) (by simp) with h2319 | h2319
                        · rcases p2316_3 (m.d 1 2) (by simp) with h2320 | h2320
                          · linarith only [h0, h2320, hlam]
                          · linarith only [h2050, h2320, hlam]
                        · linarith only [h2319, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2050, h2223, h2311, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2050, h2223, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2223, h2314, h4, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2051, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2223, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2050, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2307, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2309, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h2050, h2051, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h2050, h2051, h2223, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h3, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2050, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h2050, h2223, h2314, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2311, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                    · linarith only [h2051, h2311, h2315, h4, h5, hlam]
                  · linarith only [h2051, h2311, h2314, hlam]
              · linarith only [h2049, h2050, h2051, h2311, h5, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2349 | h2349
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2350 | h2350
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2351 | h2351
          · linarith only [h1, h2351, h5, hlam]
          · linarith only [h2050, h2349, h2351, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2354 | h2354
          · linarith only [h1, h2354, h5, hlam]
          · linarith only [h2050, h2349, h2354, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2357 | h2357
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2358 | h2358
          · linarith only [h1, h2358, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2360 | h2360
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2361 | h2361
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2362 | h2362
                · linarith only [h2362, h4, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2364 | h2364
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2365 | h2365
                    · rcases h1bigk with h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2357, h2364, hc01, hc45, hlam, hphi, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2050, h2357, h2364, hc01, hc45, hlam, hphi, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2349, h2357, h2364, hc01, hc45, hlam, hphi, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        rcases p2366_3 (m.d 0 1) (by simp) with h2371 | h2371
                        · rcases p2366_3 (m.d 1 2) (by simp) with h2372 | h2372
                          · linarith only [h0, h2372, hlam]
                          · linarith only [h2357, h2372, hlam]
                        · linarith only [h2371, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2050, hlam, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2349, hlam, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2050, h2362, h4, hc04, hc15, hlam, hphi, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h1, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2357, h2358, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2358, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h1, h2357, h2364, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h2349, h2357, h2364, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h2349, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h2349, h2357, h2364, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h3, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2357, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2360, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2361, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                    · linarith only [h0, h2357, h2364, h2365, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2049, h2349, h2364, h5, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h2050, h2357, h2358, h2361, hlam]
            · linarith only [h2050, h2357, h2360, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2400 | h2400
          · linarith only [h1, h2400, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2402 | h2402
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2403 | h2403
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2404 | h2404
                · linarith only [h2404, h4, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2406 | h2406
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2407 | h2407
                    · rcases h1bigk with h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        rcases p2408_3 (m.d 0 1) (by simp) with h2410 | h2410
                        · rcases p2408_3 (m.d 1 2) (by simp) with h2411 | h2411
                          · linarith only [h2411, hlam, p2408_0]
                          · rcases p2408_3 (m.d 1 3) (by simp) with h2413 | h2413
                            · linarith only [h1, h2413, hlam]
                            · linarith only [h2050, h2413, hlam]
                        · linarith only [h2410, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2402, hc01, hc35, hlam, hphi, ht0b, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2400, h2402, h2407, hc01, hc45, hlam, hphi, ht0b, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        rcases p2408_3 (m.d 0 1) (by simp) with h2419 | h2419
                        · rcases p2408_3 (m.d 1 2) (by simp) with h2420 | h2420
                          · linarith only [h0, h2420, hlam]
                          · rcases p2408_3 (m.d 1 3) (by simp) with h2422 | h2422
                            · linarith only [h1, h2422, hlam]
                            · linarith only [h2402, h2422, hlam]
                        · linarith only [h2419, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h0, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2050, hlam, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2349, hlam, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2357, hlam, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h1, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2400, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2050, h2357, hc12, hc23, hlam, hphi, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h0, h2349, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h0, h2349, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h0, h2349, h2357, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h3, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2408_1]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2402, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [h2403, hlam, p2408_0]
                      · have p2408_0 := h2408c.1
                        have p2408_1 := h2408c.2.1
                        have p2408_2 := h2408c.2.2.1
                        have p2408_3 := h2408c.2.2.2
                        linarith only [hlam, p2408_0]
                    · linarith only [h2049, h2407, h5, hlam]
                  · linarith only [h2349, h2403, h2406, hlam]
              · linarith only [h2400, h2402, h2403, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2449 | h2449
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2450 | h2450
                · linarith only [h2450, h4, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2452 | h2452
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2453 | h2453
                    · rcases h1bigk with h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        rcases p2454_3 (m.d 0 1) (by simp) with h2456 | h2456
                        · rcases p2454_3 (m.d 1 2) (by simp) with h2457 | h2457
                          · linarith only [h2457, hlam, p2454_0]
                          · rcases p2454_3 (m.d 1 3) (by simp) with h2459 | h2459
                            · linarith only [h1, h2459, hlam]
                            · linarith only [h2050, h2459, hlam]
                        · linarith only [h2456, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        rcases p2454_3 (m.d 0 1) (by simp) with h2463 | h2463
                        · rcases p2454_3 (m.d 1 2) (by simp) with h2464 | h2464
                          · linarith only [h0, h2464, hlam]
                          · rcases p2454_3 (m.d 1 3) (by simp) with h2466 | h2466
                            · linarith only [h2466, hlam, p2454_0]
                            · rcases p2454_3 (m.d 1 4) (by simp) with h2468 | h2468
                              · linarith only [h2, h2468, hlam]
                              · linarith only [h2400, h2468, hlam]
                        · linarith only [h2463, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2449, hc01, hc45, hlam, hphi, ht0b, ht5b, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        rcases p2454_3 (m.d 0 1) (by simp) with h2473 | h2473
                        · rcases p2454_3 (m.d 1 2) (by simp) with h2474 | h2474
                          · linarith only [h0, h2474, hlam]
                          · rcases p2454_3 (m.d 1 3) (by simp) with h2476 | h2476
                            · linarith only [h1, h2476, hlam]
                            · rcases p2454_3 (m.d 1 4) (by simp) with h2478 | h2478
                              · linarith only [h2, h2478, hlam]
                              · linarith only [h2449, h2478, hlam]
                        · linarith only [h2473, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h0, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2050, hlam, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2349, hlam, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2357, hlam, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h1, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2402, hc12, hc35, hlam, hphi, ht23, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2400, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2402, hlam, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h0, h2349, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h0, h2050, h2349, h2402, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h3, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2050, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2454_1]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [h2449, hlam, p2454_0]
                      · have p2454_0 := h2454c.1
                        have p2454_1 := h2454c.2.1
                        have p2454_2 := h2454c.2.2.1
                        have p2454_3 := h2454c.2.2.2
                        linarith only [hlam, p2454_0]
                    · linarith only [h2049, h2453, h5, hlam]
                  · linarith only [h2349, h2449, h2452, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2504 | h2504
                · linarith only [h2049, h2050, h2400, h2449, h2504, h5, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2506 | h2506
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2507 | h2507
                    · rcases h1bigk with h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        rcases p2508_3 (m.d 0 1) (by simp) with h2510 | h2510
                        · rcases p2508_3 (m.d 1 2) (by simp) with h2511 | h2511
                          · linarith only [h2511, hlam, p2508_0]
                          · rcases p2508_3 (m.d 1 3) (by simp) with h2513 | h2513
                            · linarith only [h1, h2513, hlam]
                            · linarith only [h2050, h2513, hlam]
                        · linarith only [h2510, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        rcases p2508_3 (m.d 0 1) (by simp) with h2517 | h2517
                        · rcases p2508_3 (m.d 1 2) (by simp) with h2518 | h2518
                          · linarith only [h0, h2518, hlam]
                          · rcases p2508_3 (m.d 1 3) (by simp) with h2520 | h2520
                            · linarith only [h2520, hlam, p2508_0]
                            · rcases p2508_3 (m.d 1 4) (by simp) with h2522 | h2522
                              · linarith only [h2, h2522, hlam]
                              · linarith only [h2400, h2522, hlam]
                        · linarith only [h2517, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        rcases p2508_3 (m.d 0 1) (by simp) with h2526 | h2526
                        · rcases p2508_3 (m.d 1 2) (by simp) with h2527 | h2527
                          · linarith only [h0, h2527, hlam]
                          · rcases p2508_3 (m.d 1 3) (by simp) with h2529 | h2529
                            · linarith only [h1, h2529, hlam]
                            · rcases p2508_3 (m.d 1 4) (by simp) with h2531 | h2531
                              · linarith only [h2531, hlam, p2508_0]
                              · rcases p2508_3 (m.d 1 5) (by simp) with h2533 | h2533
                                · linarith only [h2533, h3, hlam]
                                · linarith only [h2449, h2533, hlam]
                        · linarith only [h2526, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        rcases p2508_3 (m.d 0 1) (by simp) with h2537 | h2537
                        · rcases p2508_3 (m.d 1 2) (by simp) with h2538 | h2538
                          · linarith only [h0, h2538, hlam]
                          · rcases p2508_3 (m.d 1 3) (by simp) with h2540 | h2540
                            · linarith only [h1, h2540, hlam]
                            · rcases p2508_3 (m.d 1 4) (by simp) with h2542 | h2542
                              · linarith only [h2, h2542, hlam]
                              · rcases p2508_3 (m.d 1 5) (by simp) with h2544 | h2544
                                · linarith only [h2544, hlam, p2508_0]
                                · rcases h4bigk with h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    rcases p2546_3 (m.d 0 4) (by simp) with h2548 | h2548
                                    · rcases p2546_3 (m.d 1 4) (by simp) with h2549 | h2549
                                      · linarith only [h2, h2549, hlam]
                                      · rcases p2546_3 (m.d 2 4) (by simp) with h2551 | h2551
                                        · linarith only [h2551, h4, hlam]
                                        · linarith only [h2349, h2551, hlam]
                                    · linarith only [h2, h2548, hlam]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2050, h2400, h2449, h2506, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h5, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2050, h2400, h2449, h5, hc12, hc34, hlam, hphi, ht23, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2349, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2400, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2449, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h4, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    rcases p2546_3 (m.d 0 4) (by simp) with h2564 | h2564
                                    · rcases p2546_3 (m.d 1 4) (by simp) with h2565 | h2565
                                      · linarith only [h2349, h2565, hlam]
                                      · rcases p2546_3 (m.d 2 4) (by simp) with h2567 | h2567
                                        · rcases p2546_3 (m.d 3 4) (by simp) with h2568 | h2568
                                          · rcases p2546_3 (m.d 4 5) (by simp) with h2569 | h2569
                                            · linarith only [h2506, h2569, hlam]
                                            · linarith only [h2449, h2569, hlam]
                                          · linarith only [h2400, h2568, hlam]
                                        · linarith only [h2349, h2567, hlam]
                                    · linarith only [h2, h2564, hlam]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2504, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2050, h2400, h2449, hc12, hc24, hlam, hphi, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2049, h2050, h2400, h2449, hc12, hc34, hlam, hphi, ht23, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    rcases p2546_3 (m.d 0 4) (by simp) with h2579 | h2579
                                    · linarith only [h2579, h5, hlam]
                                    · linarith only [h2, h2579, hlam]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2050, h2400, h2449, h2506, hc12, hc34, hlam, hphi, ht23, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2050, h2400, h2449, hc12, hc34, hlam, hphi, ht23, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2049, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2050, h2400, h2506, hc12, hc24, hlam, hphi, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2506, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2507, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                        · linarith only [h2537, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h0, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2050, hlam, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2349, hlam, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2357, hlam, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h1, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2400, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2402, hlam, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h0, h2349, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2449, hlam, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h3, hlam, p2508_0]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h2050, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [h0, h2449, h2506, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2508_1]
                      · have p2508_0 := h2508c.1
                        have p2508_1 := h2508c.2.1
                        have p2508_2 := h2508c.2.2.1
                        have p2508_3 := h2508c.2.2.2
                        linarith only [hlam, p2508_0]
                    · linarith only [h0, h2506, h2507, h4, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2049, h2349, h2506, h5, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2613 | h2613
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2614 | h2614
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2615 | h2615
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2616 | h2616
          · linarith only [h1, h2616, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2618 | h2618
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2619 | h2619
              · linarith only [h2, h2049, h2619, hlam]
              · linarith only [h2616, h2618, h2619, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2622 | h2622
              · linarith only [h2, h2049, h2622, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2624 | h2624
                · linarith only [h1, h2613, h2624, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2626 | h2626
                  · linarith only [h0, h2049, h2614, h2626, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2628 | h2628
                    · rcases h1bigk with h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2615, h2624, h2626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        rcases p2629_3 (m.d 0 1) (by simp) with h2632 | h2632
                        · rcases p2629_3 (m.d 1 2) (by simp) with h2633 | h2633
                          · linarith only [h0, h2633, hlam]
                          · linarith only [h2613, h2633, hlam]
                        · linarith only [h2632, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        rcases p2629_3 (m.d 0 1) (by simp) with h2637 | h2637
                        · rcases p2629_3 (m.d 1 2) (by simp) with h2638 | h2638
                          · linarith only [h0, h2638, hlam]
                          · linarith only [h2614, h2638, hlam]
                        · linarith only [h2637, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        rcases p2629_3 (m.d 0 1) (by simp) with h2642 | h2642
                        · rcases p2629_3 (m.d 1 2) (by simp) with h2643 | h2643
                          · linarith only [h0, h2643, hlam]
                          · linarith only [h2615, h2643, hlam]
                        · linarith only [h2642, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h0, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h0, h2613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h1, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2613, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2616, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2618, hlam, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2614, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2, h2613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2622, hlam, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h3, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2615, hlam, p2629_0]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2613, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [h2049, h2628, h3, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2629_1]
                      · have p2629_0 := h2629c.1
                        have p2629_1 := h2629c.2.1
                        have p2629_2 := h2629c.2.2.1
                        have p2629_3 := h2629c.2.2.2
                        linarith only [hlam, p2629_0]
                    · rcases h1bigk with h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2670 | h2670
                        · rcases p2667_3 (m.d 1 2) (by simp) with h2671 | h2671
                          · linarith only [h0, h2671, hlam]
                          · linarith only [h2613, h2671, hlam]
                        · linarith only [h2670, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2675 | h2675
                        · rcases p2667_3 (m.d 1 2) (by simp) with h2676 | h2676
                          · linarith only [h0, h2676, hlam]
                          · linarith only [h2614, h2676, hlam]
                        · linarith only [h2675, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        rcases p2667_3 (m.d 0 1) (by simp) with h2680 | h2680
                        · rcases p2667_3 (m.d 1 2) (by simp) with h2681 | h2681
                          · linarith only [h0, h2681, hlam]
                          · linarith only [h2615, h2681, hlam]
                        · linarith only [h2680, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h0, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h0, h2613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h0, h2614, h2624, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h1, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2613, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2616, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2618, hlam, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2614, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2, h2613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2622, hlam, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h3, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2615, hlam, p2667_0]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2613, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [h2049, h3, hc14, hc45, hlam, hphi, p2667_1]
                      · have p2667_0 := h2667c.1
                        have p2667_1 := h2667c.2.1
                        have p2667_2 := h2667c.2.2.1
                        have p2667_3 := h2667c.2.2.2
                        linarith only [hlam, p2667_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2705 | h2705
          · linarith only [h1, h2705, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2707 | h2707
            · linarith only [h2613, h2615, h2707, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2709 | h2709
              · linarith only [h2, h2049, h2709, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2711 | h2711
                · linarith only [h1, h2613, h2711, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2713 | h2713
                  · linarith only [h0, h2, h2049, h2614, h2713, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2715 | h2715
                    · linarith only [h2614, h2615, h2711, h2713, h2715, hc23, hc34, hlam, hphi]
                    · rcases h1bigk with h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2614, h2711, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        rcases p2717_3 (m.d 0 1) (by simp) with h2720 | h2720
                        · rcases p2717_3 (m.d 1 2) (by simp) with h2721 | h2721
                          · linarith only [h0, h2721, hlam]
                          · linarith only [h2613, h2721, hlam]
                        · linarith only [h2720, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        rcases p2717_3 (m.d 0 1) (by simp) with h2725 | h2725
                        · rcases p2717_3 (m.d 1 2) (by simp) with h2726 | h2726
                          · linarith only [h0, h2726, hlam]
                          · linarith only [h2614, h2726, hlam]
                        · linarith only [h2725, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2614, h2615, h2711, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h0, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2613, h2615, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2613, h2615, h2705, h2713, hc23, hc45, hlam, hphi, ht34, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2615, hlam, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h1, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2613, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2705, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2707, hlam, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2614, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2, h2613, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2709, hlam, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h3, hlam, p2717_0]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2707, hc12, hc35, hlam, hphi, ht23, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h2613, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2717_1]
                      · have p2717_0 := h2717c.1
                        have p2717_1 := h2717c.2.1
                        have p2717_2 := h2717c.2.2.1
                        have p2717_3 := h2717c.2.2.2
                        linarith only [hlam, p2717_0]
      · linarith only [h2049, h2613, h2614, h4, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2752 | h2752
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2753 | h2753
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2754 | h2754
          · linarith only [h1, h2754, h5, hlam]
          · linarith only [h2613, h2752, h2754, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2757 | h2757
          · linarith only [h1, h2757, h5, hlam]
          · linarith only [h2613, h2752, h2757, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2760 | h2760
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2761 | h2761
          · linarith only [h1, h2761, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2763 | h2763
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2764 | h2764
              · linarith only [h2049, h2752, h2760, h2764, h4, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h2752, h2760, h2764, hlam]
            · linarith only [h2613, h2760, h2763, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2768 | h2768
          · linarith only [h1, h2768, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2770 | h2770
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2771 | h2771
              · linarith only [h2, h2049, h2752, h2771, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h2768, h2770, h2771, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2774 | h2774
              · linarith only [h2049, h2752, h2774, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2776 | h2776
                · linarith only [h2776, h4, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2778 | h2778
                  · linarith only [h2049, h2778, h4, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2780 | h2780
                    · linarith only [h2049, h2752, h2780, h4, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2613, h2776, h2780, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_21_14_H_I_L_I_s4_x0 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5
  · exact r1l7_21_14_H_I_L_I_s4_x1 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5

set_option maxHeartbeats 8564000 in
set_option maxHeartbeats 8564000 in
theorem r1l7_21_14_H_I_L_I_s3_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_21_14_H_I_L_I_s4 m hb1 hb4 h0 h1 h2 h3 h4

end R2N4
