import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1865 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h2070 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h2071 | h2071
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2072 | h2072
    · linarith only [h0, h2, h2072, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2074 | h2074
      · linarith only [h1865, h2072, h2074, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2076 | h2076
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2077 | h2077
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2078 | h2078
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2079 | h2079
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2080 | h2080
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2081 | h2081
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2082 | h2082
                    · rcases h5bigk with h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c | h2083c
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h0, h2071, h2074, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2083_1, u1elo0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h1865, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p2083_1, u1elo0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h0, h2071, hc45, hlam, hphi, ht01, ht0b, ht5b, p2083_1, u1elo0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h1, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2074, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p2083_1, u1elo4]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h0, h2078, hc45, hlam, hphi, ht01, ht0b, ht5b, p2083_1, u1elo0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2083_1]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2074, hc12, hc25, hlam, hphi, p2083_1]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        rcases p2083_3 (m.d 0 5) (by simp) with h2097 | h2097
                        · linarith only [h1865, h2097, hlam]
                        · linarith only [h2070, h2097, hlam]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        rcases p2083_3 (m.d 0 5) (by simp) with h2100 | h2100
                        · linarith only [h1865, h2100, hlam]
                        · linarith only [h2071, h2100, hlam]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2070, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2077, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2080, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht0b, ht5b, p2083_1]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2071, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2078, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2081, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [h2082, hlam, p2083_0]
                      · have p2083_0 := h2083c.1
                        have p2083_1 := h2083c.2.1
                        have p2083_2 := h2083c.2.2.1
                        have p2083_3 := h2083c.2.2.2
                        linarith only [hlam, p2083_0]
                    · linarith only [h0, h2078, h2082, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2078, h2081, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h2077, h2079, h2080, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h2, h2076, h2079, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2117 | h2117
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2118 | h2118
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2119 | h2119
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2120 | h2120
                    · linarith only [h2072, h2076, h2078, h2120, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases h5bigk with h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h2071, hc15, hlam, hphi, ht01, ht0b, ht5b, p2122_1, u1elo0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1865, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h2071, hc35, hlam, hphi, ht01, ht0b, ht5b, p2122_1, u1elo0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h2071, h2072, h2078, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2122_1, u1elo0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2074, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p2122_1, u1elo4]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2078, hlam, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1865, h2117, h2119, hc02, hc23, hlam, hphi, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2074, h2117, h2119, hc12, hc23, hlam, hphi, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        rcases p2122_3 (m.d 0 5) (by simp) with h2136 | h2136
                        · linarith only [h1865, h2136, hlam]
                        · linarith only [h2070, h2136, hlam]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2072, h2078, h2117, h2119, hc12, hc23, hlam, hphi, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2070, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2077, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2118, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2120, hlam, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2071, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2072, h2078, hc12, hc45, hlam, hphi, ht23, ht34, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2119, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h2071, h2120, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2122_1, u1elo0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                  · linarith only [h0, h2, h2071, h2119, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1, h2077, h2117, h2118, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h2071, h2076, h2078, h2117, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2153 | h2153
            · linarith only [h2076, h2077, h2153, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2155 | h2155
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2156 | h2156
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2157 | h2157
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2158 | h2158
                    · linarith only [h2076, h2153, h2158, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · linarith only [h0, h2071, h2076, h2077, h2158, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2, h2071, h2157, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h2070, h2071, h2155, h2156, hlam]
              · linarith only [h0, h2070, h2071, h2076, h2077, h2155, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2164 | h2164
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2165 | h2165
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2166 | h2166
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2167 | h2167
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2168 | h2168
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2169 | h2169
                    · rcases h5bigk with h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c | h2170c
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h0, h2071, hc15, hlam, hphi, ht01, ht0b, ht5b, p2170_1, u1elo0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h1865, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h0, h2071, h2169, hc45, hlam, hphi, ht01, ht0b, ht5b, p2170_1, u1elo0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h0, h2071, hc45, hlam, hphi, ht01, ht0b, ht5b, p2170_1, u1elo0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h1, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2074, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2169, hc45, hlam, hphi, ht01, ht0b, ht5b, p2170_1, u1elo4]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2164, hc45, hlam, hphi, ht01, ht0b, ht5b, p2170_1, u1elo2]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h1865, h2168, hc02, hc24, hlam, hphi, p2170_1]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2074, h2168, hc12, hc24, hlam, hphi, p2170_1]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        rcases p2170_3 (m.d 0 5) (by simp) with h2184 | h2184
                        · linarith only [h1865, h2184, hlam]
                        · linarith only [h2070, h2184, hlam]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        rcases p2170_3 (m.d 0 5) (by simp) with h2187 | h2187
                        · linarith only [h1865, h2187, hlam]
                        · linarith only [h2071, h2187, hlam]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2070, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2164, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2167, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht0b, ht5b, p2170_1]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2071, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2165, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2168, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [h2169, hlam, p2170_0]
                      · have p2170_0 := h2170c.1
                        have p2170_1 := h2170c.2.1
                        have p2170_2 := h2170c.2.2.1
                        have p2170_3 := h2170c.2.2.2
                        linarith only [hlam, p2170_0]
                    · linarith only [h0, h2071, h2076, h2169, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2165, h2168, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h2076, h2164, h2167, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2203 | h2203
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2204 | h2204
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2205 | h2205
                    · rcases h5bigk with h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h1, h2074, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2206_1, u1elo0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h1865, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h1865, h2166, h2203, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h1865, h2166, h2203, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h1, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2074, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2205, hc45, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u1elo4]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h0, h2076, h2164, hc45, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u1elo0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2166, h2203, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2166, h2203, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2166, h2203, h2205, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2166, h2203, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2070, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2164, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2203, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht0b, ht5b, p2206_1]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2071, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2165, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2204, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [h2205, hlam, p2206_0]
                      · have p2206_0 := h2206c.1
                        have p2206_1 := h2206c.2.1
                        have p2206_2 := h2206c.2.2.1
                        have p2206_3 := h2206c.2.2.2
                        linarith only [hlam, p2206_0]
                    · linarith only [h1865, h2166, h2203, h2205, hc02, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h2, h2165, h2204, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h2076, h2164, h2203, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h2071, h2076, h2164, h2165, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2236 | h2236
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2237 | h2237
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2238 | h2238
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2239 | h2239
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2240 | h2240
                    · rcases h5bigk with h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h1865, h2074, hc12, hc25, hlam, hphi, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h1865, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2164, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h0, h2071, hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1, u1elo0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h1, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2074, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2164, hlam, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1, u1elo4]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2074, hc12, hc25, hlam, hphi, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2164, h2238, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        rcases p2241_3 (m.d 0 5) (by simp) with h2256 | h2256
                        · linarith only [h1865, h2256, hlam]
                        · linarith only [h2071, h2256, hlam]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2070, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2074, h2240, hc12, hc34, hlam, hphi, ht23, p2241_1]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2238, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h0, h2070, h2071, hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1, u1elo0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2071, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2236, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2239, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [h2240, hlam, p2241_0]
                      · have p2241_0 := h2241c.1
                        have p2241_1 := h2241c.2.1
                        have p2241_2 := h2241c.2.2.1
                        have p2241_3 := h2241c.2.2.2
                        linarith only [hlam, p2241_0]
                    · linarith only [h0, h2236, h2240, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2236, h2239, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h2070, h2071, h2076, h2236, h2237, h2238, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2272 | h2272
                · linarith only [h2164, h2237, h2272, hc13, hc34, hlam, hphi]
                · linarith only [h1865, h2070, h2272, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2275 | h2275
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2276 | h2276
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2277 | h2277
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2278 | h2278
                    · linarith only [h2072, h2236, h2275, h2278, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h2071, h2076, h2278, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h2, h2071, h2277, hlam]
                · linarith only [h2076, h2275, h2276, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2283 | h2283
                · linarith only [h2164, h2275, h2283, hc13, hc34, hlam, hphi]
                · linarith only [h1865, h2070, h2283, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2286 | h2286
    · linarith only [h0, h2, h2286, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2288 | h2288
      · linarith only [h1865, h2286, h2288, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2290 | h2290
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2291 | h2291
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2292 | h2292
            · linarith only [h0, h2071, h2292, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2294 | h2294
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2295 | h2295
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2296 | h2296
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2297 | h2297
                    · linarith only [h0, h2071, h2290, h2297, hlam]
                    · rcases h5bigk with h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h1, h2286, h2292, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2299_1, u1elo0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h1865, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p2299_1, u1elo0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2071, hlam, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h1, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2288, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p2299_1, u1elo4]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2292, hlam, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2288, hc12, hc25, hlam, hphi, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        rcases p2299_3 (m.d 0 5) (by simp) with h2313 | h2313
                        · linarith only [h1865, h2313, hlam]
                        · linarith only [h2070, h2313, hlam]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h0, h2071, h2286, h2294, h2296, hc12, hc23, hlam, hphi, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2070, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2291, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2295, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2297, hlam, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h0, h2071, h2286, hc12, hc45, hlam, hphi, ht23, ht34, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2286, h2292, hc12, hc45, hlam, hphi, ht23, ht34, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2296, hlam, p2299_0]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [h2294, h2296, h2297, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2299_1]
                      · have p2299_0 := h2299c.1
                        have p2299_1 := h2299c.2.1
                        have p2299_2 := h2299c.2.2.1
                        have p2299_3 := h2299c.2.2.2
                        linarith only [hlam, p2299_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2327 | h2327
                    · linarith only [h2286, h2296, h2327, hc12, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c | h2329c
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2329_1, u1elo0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h1865, hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h1, h2327, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2329_1, u1elo0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2071, hlam, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h1, hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2288, hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2327, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2329_1, u1elo4]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2292, hlam, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h1865, h2296, hc02, hc45, hlam, hphi, ht23, ht34, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2288, h2296, hc12, hc45, hlam, hphi, ht23, ht34, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2296, h2327, hc34, hc45, hlam, hphi, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2296, hlam, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2070, hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2291, hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2295, hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [hlam, p2329_0]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2327, hlam, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h0, h2071, h2286, hc12, hc45, hlam, hphi, ht23, ht34, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2286, h2292, hc12, hc45, hlam, hphi, ht23, ht34, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h1865, hc02, hc45, hlam, hphi, ht23, ht34, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [h2327, hc34, hc45, hlam, hphi, p2329_1]
                      · have p2329_0 := h2329c.1
                        have p2329_1 := h2329c.2.1
                        have p2329_2 := h2329c.2.2.1
                        have p2329_3 := h2329c.2.2.2
                        linarith only [hlam, p2329_0]
                · linarith only [h1, h2291, h2294, h2295, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h2, h2290, h2294, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2357 | h2357
            · linarith only [h0, h2071, h2357, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2359 | h2359
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2360 | h2360
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2361 | h2361
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2362 | h2362
                    · linarith only [h2070, h2071, h2290, h2291, h2362, hlam]
                    · rcases h5bigk with h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2071, h2359, h2361, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h1865, hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2071, h2291, h2359, h2361, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2071, hlam, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h1, hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2288, hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2291, hlam, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2357, hlam, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2288, hc12, hc25, hlam, hphi, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2290, h2291, h2360, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2071, h2359, h2361, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2070, hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2070, h2290, h2291, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2360, hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2362, hlam, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h1, h2290, h2291, hc34, hc45, hlam, hphi, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2290, h2291, hc34, hc45, hlam, hphi, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2361, hlam, p2364_0]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [h2290, h2291, h2359, h2361, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2364_1]
                      · have p2364_0 := h2364c.1
                        have p2364_1 := h2364c.2.1
                        have p2364_2 := h2364c.2.2.1
                        have p2364_3 := h2364c.2.2.2
                        linarith only [hlam, p2364_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2390 | h2390
                    · linarith only [h2070, h2290, h2291, h2361, h2390, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h5bigk with h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2392_1, u1elo0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1865, hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1865, h2291, h2361, hc13, hc45, hlam, hphi, ht34, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2071, hlam, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1, hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2288, hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2291, hlam, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2357, hlam, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1865, h2361, hc02, hc45, hlam, hphi, ht23, ht34, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2288, h2361, hc12, hc45, hlam, hphi, ht23, ht34, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2290, h2291, h2361, hc34, hc45, hlam, hphi, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2361, hlam, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2070, hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2070, h2290, h2291, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2360, hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [hlam, p2392_0]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2390, hlam, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1, h2290, h2291, hc34, hc45, hlam, hphi, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2290, h2291, hc34, hc45, hlam, hphi, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h1865, hc02, hc45, hlam, hphi, ht23, ht34, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [h2290, h2291, hc34, hc45, hlam, hphi, p2392_1]
                      · have p2392_0 := h2392c.1
                        have p2392_1 := h2392c.2.1
                        have p2392_2 := h2392c.2.2.1
                        have p2392_3 := h2392c.2.2.2
                        linarith only [hlam, p2392_0]
                · linarith only [h1865, h2070, h2360, hlam]
              · linarith only [h1, h2290, h2291, h2359, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2420 | h2420
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2421 | h2421
            · linarith only [h0, h2071, h2421, hlam]
            · linarith only [h2290, h2420, h2421, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2424 | h2424
            · linarith only [h0, h2070, h2071, h2420, h2424, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2426 | h2426
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2427 | h2427
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2428 | h2428
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2429 | h2429
                    · linarith only [h2, h2071, h2426, h2429, hc02, hc23, hlam, hphi]
                    · rcases h5bigk with h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c | h2431c
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2431_1, u1elo0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h1865, hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2290, h2429, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2071, hlam, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h1, hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2288, hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2420, hlam, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2424, hlam, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2288, hc12, hc25, hlam, hphi, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2290, h2427, h2429, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2290, h2426, h2428, h2429, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2070, hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2286, h2424, hc12, hc35, hlam, hphi, ht23, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2427, hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2429, hlam, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h1, h2286, h2424, hc12, hc45, hlam, hphi, ht23, ht34, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2286, h2424, hc12, hc45, hlam, hphi, ht23, ht34, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2428, hlam, p2431_0]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [h2420, h2426, h2428, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2431_1]
                      · have p2431_0 := h2431c.1
                        have p2431_1 := h2431c.2.1
                        have p2431_2 := h2431c.2.2.1
                        have p2431_3 := h2431c.2.2.2
                        linarith only [hlam, p2431_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2457 | h2457
                    · linarith only [h2, h2428, h2457, hc02, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h1, h2286, h2424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2459_1, u1elo0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h1865, hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2290, h2457, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2071, hlam, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h1, hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2288, hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2420, hlam, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2424, hlam, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h1, h2286, h2424, h2428, hc12, hc45, hlam, hphi, ht23, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2286, h2424, h2428, hc12, hc45, hlam, hphi, ht23, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2290, h2428, h2457, hc13, hc45, hlam, hphi, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2428, hlam, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2070, hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2286, h2424, hc12, hc35, hlam, hphi, ht23, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2427, hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [hlam, p2459_0]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2457, hlam, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h1, h2286, h2424, hc12, hc45, hlam, hphi, ht23, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2286, h2424, hc12, hc45, hlam, hphi, ht23, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h1865, hc02, hc45, hlam, hphi, ht23, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [h2420, hc13, hc45, hlam, hphi, ht34, p2459_1]
                      · have p2459_0 := h2459c.1
                        have p2459_1 := h2459c.2.1
                        have p2459_2 := h2459c.2.2.1
                        have p2459_3 := h2459c.2.2.2
                        linarith only [hlam, p2459_0]
                · linarith only [h2290, h2426, h2427, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2486 | h2486
                · linarith only [h2420, h2426, h2486, hc13, hc34, hlam, hphi]
                · linarith only [h1865, h2070, h2486, hlam]

end R2N4
