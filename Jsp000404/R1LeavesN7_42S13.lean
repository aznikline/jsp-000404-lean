import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1658 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2081 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2082 | h2082
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2083 | h2083
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2084 | h2084
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2085 | h2085
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2086 | h2086
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2087 | h2087
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2088 | h2088
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2089 | h2089
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2090 | h2090
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2091 | h2091
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2092 | h2092
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2093 | h2093
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2094 | h2094
                          · rcases h2bigk with h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2091, h2094, hc02, hc45, hlam, hphi, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, h2091, h2094, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              rcases p2095_3 (m.d 0 2) (by simp) with h2100 | h2100
                              · rcases p2095_3 (m.d 1 2) (by simp) with h2101 | h2101
                                · rcases p2095_3 (m.d 2 3) (by simp) with h2102 | h2102
                                  · linarith only [h2081, h2102, hlam]
                                  · linarith only [h2092, h2102, hlam]
                                · linarith only [h2088, h2101, hlam]
                              · linarith only [h2100, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2091, h2094, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2091, h2094, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              rcases p2095_3 (m.d 0 2) (by simp) with h2111 | h2111
                              · linarith only [h0, h2111, hlam]
                              · linarith only [h2083, h2111, hlam]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2081, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2086, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2081, h2091, h2094, hc02, hc45, hlam, hphi, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, h2081, h2092, h2094, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2082, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2087, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2091, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, h2082, h2092, h2094, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2083, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2088, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2092, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2093, hlam, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                          · rcases h2bigk with h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h0, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h0, h2091, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h0, h2093, h2094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h0, h2093, h2094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2092, h2093, h2094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2093, h2094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2093, h2094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2081, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2086, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2093, h2094, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2081, h2093, h2094, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2082, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2087, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2091, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2082, h2093, h2094, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2083, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2088, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2092, hlam, p2129_0]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [h2093, hlam, p2129_1]
                            · have p2129_0 := h2129c.1
                              have p2129_1 := h2129c.2.1
                              have p2129_2 := h2129c.2.2.1
                              have p2129_3 := h2129c.2.2.2
                              linarith only [hlam, p2129_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2155 | h2155
                          · linarith only [h0, h2081, h2091, h2093, h2155, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h2bigk with h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h0, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h0, h2091, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2157_1]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              rcases p2157_3 (m.d 0 2) (by simp) with h2161 | h2161
                              · rcases p2157_3 (m.d 1 2) (by simp) with h2162 | h2162
                                · rcases p2157_3 (m.d 2 3) (by simp) with h2163 | h2163
                                  · linarith only [h2081, h2163, hlam]
                                  · linarith only [h2091, h2163, hlam]
                                · linarith only [h2087, h2162, hlam]
                              · linarith only [h2161, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              rcases p2157_3 (m.d 0 2) (by simp) with h2168 | h2168
                              · rcases p2157_3 (m.d 1 2) (by simp) with h2169 | h2169
                                · rcases p2157_3 (m.d 2 3) (by simp) with h2170 | h2170
                                  · linarith only [h2081, h2170, hlam]
                                  · linarith only [h2092, h2170, hlam]
                                · linarith only [h2088, h2169, hlam]
                              · linarith only [h2168, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2157_1]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2092, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2157_1]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              rcases p2157_3 (m.d 0 2) (by simp) with h2178 | h2178
                              · linarith only [h0, h2178, hlam]
                              · linarith only [h2082, h2178, hlam]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              rcases p2157_3 (m.d 0 2) (by simp) with h2181 | h2181
                              · linarith only [h0, h2181, hlam]
                              · linarith only [h2083, h2181, hlam]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2081, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2086, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2081, h2091, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2157_1]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h0, h2081, h2091, h2093, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2157_1]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2082, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2087, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2091, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2093, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2083, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2088, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2092, hlam, p2157_0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [h2083, h2091, hc34, hlam, hphi, ht45, p2157_1, u5elo0]
                            · have p2157_0 := h2157c.1
                              have p2157_1 := h2157c.2.1
                              have p2157_2 := h2157c.2.2.1
                              have p2157_3 := h2157c.2.2.2
                              linarith only [hlam, p2157_0]
                      · linarith only [h2085, h2091, h2092, hc34, hlam, hphi, ht45, u5elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2200 | h2200
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2201 | h2201
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2202 | h2202
                          · rcases h2bigk with h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c | h2203c
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h0, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h0, h2200, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h0, h2091, h2200, h2202, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              rcases p2203_3 (m.d 0 2) (by simp) with h2208 | h2208
                              · rcases p2203_3 (m.d 1 2) (by simp) with h2209 | h2209
                                · rcases p2203_3 (m.d 2 3) (by simp) with h2210 | h2210
                                  · linarith only [h2081, h2210, hlam]
                                  · linarith only [h2200, h2210, hlam]
                                · linarith only [h2088, h2209, hlam]
                              · linarith only [h2208, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2200, h2202, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2091, h2200, h2202, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              rcases p2203_3 (m.d 0 2) (by simp) with h2219 | h2219
                              · linarith only [h0, h2219, hlam]
                              · linarith only [h2083, h2219, hlam]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2081, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2086, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2091, hlam, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2081, h2200, h2202, hc02, hc45, hlam, hphi, ht0b, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2082, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2087, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2082, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h1658, h2084, h2086, h2091, h2200, h2202, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2083, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2088, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2200, hlam, p2203_0]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [h2201, hlam, p2203_1]
                            · have p2203_0 := h2203c.1
                              have p2203_1 := h2203c.2.1
                              have p2203_2 := h2203c.2.2.1
                              have p2203_3 := h2203c.2.2.2
                              linarith only [hlam, p2203_0]
                          · linarith only [h2091, h2200, h2202, hc35, hlam, hphi, u5elo4]
                        · linarith only [h2091, h2200, h2201, hc35, hlam, hphi, u5elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2239 | h2239
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2240 | h2240
                          · rcases h2bigk with h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h0, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              rcases p2241_3 (m.d 0 2) (by simp) with h2244 | h2244
                              · rcases p2241_3 (m.d 1 2) (by simp) with h2245 | h2245
                                · rcases p2241_3 (m.d 2 3) (by simp) with h2246 | h2246
                                  · linarith only [h2246, hlam, p2241_0]
                                  · rcases p2241_3 (m.d 2 4) (by simp) with h2248 | h2248
                                    · linarith only [h2082, h2248, hlam]
                                    · linarith only [h2091, h2248, hlam]
                                · linarith only [h2086, h2245, hlam]
                              · linarith only [h2244, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h0, h2239, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              rcases p2241_3 (m.d 0 2) (by simp) with h2254 | h2254
                              · rcases p2241_3 (m.d 1 2) (by simp) with h2255 | h2255
                                · rcases p2241_3 (m.d 2 3) (by simp) with h2256 | h2256
                                  · linarith only [h2081, h2256, hlam]
                                  · rcases p2241_3 (m.d 2 4) (by simp) with h2258 | h2258
                                    · linarith only [h2082, h2258, hlam]
                                    · linarith only [h2239, h2258, hlam]
                                · linarith only [h2088, h2255, hlam]
                              · linarith only [h2254, hlam, p2241_0]
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
                              rcases p2241_3 (m.d 0 2) (by simp) with h2265 | h2265
                              · linarith only [h0, h2265, hlam]
                              · linarith only [h2081, h2265, hlam]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2239, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              rcases p2241_3 (m.d 0 2) (by simp) with h2269 | h2269
                              · linarith only [h0, h2269, hlam]
                              · linarith only [h2083, h2269, hlam]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2081, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2086, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2091, hlam, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2200, hlam, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2082, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2087, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2082, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2084, h2091, h2200, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2083, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2088, hlam, p2241_0]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, ht45, p2241_1, u5elo2]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [h2239, hlam, p2241_1]
                            · have p2241_0 := h2241c.1
                              have p2241_1 := h2241c.2.1
                              have p2241_2 := h2241c.2.2.1
                              have p2241_3 := h2241c.2.2.2
                              linarith only [hlam, p2241_0]
                          · linarith only [h2091, h2240, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2288 | h2288
                          · rcases h2bigk with h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c | h2289c
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h0, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              rcases p2289_3 (m.d 0 2) (by simp) with h2292 | h2292
                              · rcases p2289_3 (m.d 1 2) (by simp) with h2293 | h2293
                                · rcases p2289_3 (m.d 2 3) (by simp) with h2294 | h2294
                                  · linarith only [h2294, hlam, p2289_0]
                                  · rcases p2289_3 (m.d 2 4) (by simp) with h2296 | h2296
                                    · linarith only [h2082, h2296, hlam]
                                    · linarith only [h2091, h2296, hlam]
                                · linarith only [h2086, h2293, hlam]
                              · linarith only [h2292, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              rcases p2289_3 (m.d 0 2) (by simp) with h2301 | h2301
                              · rcases p2289_3 (m.d 1 2) (by simp) with h2302 | h2302
                                · rcases p2289_3 (m.d 2 3) (by simp) with h2303 | h2303
                                  · linarith only [h2081, h2303, hlam]
                                  · rcases p2289_3 (m.d 2 4) (by simp) with h2305 | h2305
                                    · linarith only [h2305, hlam, p2289_0]
                                    · rcases p2289_3 (m.d 2 5) (by simp) with h2307 | h2307
                                      · linarith only [h2083, h2307, hlam]
                                      · linarith only [h2239, h2307, hlam]
                                · linarith only [h2087, h2302, hlam]
                              · linarith only [h2301, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              rcases p2289_3 (m.d 0 2) (by simp) with h2312 | h2312
                              · rcases p2289_3 (m.d 1 2) (by simp) with h2313 | h2313
                                · rcases p2289_3 (m.d 2 3) (by simp) with h2314 | h2314
                                  · linarith only [h2081, h2314, hlam]
                                  · rcases p2289_3 (m.d 2 4) (by simp) with h2316 | h2316
                                    · linarith only [h2082, h2316, hlam]
                                    · rcases p2289_3 (m.d 2 5) (by simp) with h2318 | h2318
                                      · linarith only [h2318, hlam, p2289_0]
                                      · rcases h3bigk with h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h1658, hlam, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2084, h2091, h2239, h2288, hlam, p2320_2]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h1658, h2086, h2239, h2288, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          rcases p2320_3 (m.d 0 3) (by simp) with h2325 | h2325
                                          · rcases p2320_3 (m.d 1 3) (by simp) with h2326 | h2326
                                            · rcases p2320_3 (m.d 2 3) (by simp) with h2327 | h2327
                                              · linarith only [h2081, h2327, hlam]
                                              · rcases p2320_3 (m.d 3 4) (by simp) with h2329 | h2329
                                                · linarith only [h2084, h2329, hlam]
                                                · linarith only [h2288, h2329, hlam]
                                            · linarith only [h2090, h2326, hlam]
                                          · linarith only [h2325, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2084, h2086, h2091, h2239, h2288, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h1658, h2084, h2091, h2239, h2288, hlam, p2320_2]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2091, h2239, h2288, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          rcases p2320_3 (m.d 0 3) (by simp) with h2338 | h2338
                                          · linarith only [h1658, h2338, hlam]
                                          · linarith only [h2085, h2338, hlam]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2081, hlam, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2086, hlam, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2091, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2200, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2084, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2089, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          rcases p2320_3 (m.d 0 3) (by simp) with h2348 | h2348
                                          · rcases p2320_3 (m.d 1 3) (by simp) with h2349 | h2349
                                            · rcases p2320_3 (m.d 2 3) (by simp) with h2350 | h2350
                                              · linarith only [h2350, hlam, p2320_0]
                                              · rcases p2320_3 (m.d 3 4) (by simp) with h2352 | h2352
                                                · rcases p2320_3 (m.d 3 5) (by simp) with h2353 | h2353
                                                  · linarith only [h2288, h2353, hlam]
                                                  · linarith only [h2200, h2353, hlam]
                                                · linarith only [h2352, hlam, p2320_0]
                                            · linarith only [h2086, h2349, hlam]
                                          · linarith only [h2081, h2348, hlam]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2084, h2091, h2239, h2288, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2085, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2090, hlam, p2320_0]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2090, hc23, hlam, hphi, ht34, ht45, p2320_1, u5elo1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [h2288, hlam, p2320_1]
                                        · have p2320_0 := h2320c.1
                                          have p2320_1 := h2320c.2.1
                                          have p2320_2 := h2320c.2.2.1
                                          have p2320_3 := h2320c.2.2.2
                                          linarith only [hlam, p2320_0]
                                · linarith only [h2088, h2313, hlam]
                              · linarith only [h2312, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2289_1]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              rcases p2289_3 (m.d 0 2) (by simp) with h2370 | h2370
                              · linarith only [h0, h2370, hlam]
                              · linarith only [h2081, h2370, hlam]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              rcases p2289_3 (m.d 0 2) (by simp) with h2373 | h2373
                              · linarith only [h0, h2373, hlam]
                              · linarith only [h2082, h2373, hlam]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              rcases p2289_3 (m.d 0 2) (by simp) with h2376 | h2376
                              · linarith only [h0, h2376, hlam]
                              · linarith only [h2083, h2376, hlam]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2081, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2086, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2091, hlam, p2289_1]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2200, hlam, p2289_1]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2082, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2087, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2239, hc23, hc45, hlam, hphi, ht34, p2289_1]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2239, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2083, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2088, hlam, p2289_0]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2090, h2200, hc23, hlam, hphi, ht34, ht45, p2289_1, u5elo1]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [h2090, h2200, hc24, hlam, hphi, ht45, p2289_1, u5elo1]
                            · have p2289_0 := h2289c.1
                              have p2289_1 := h2289c.2.1
                              have p2289_2 := h2289c.2.2.1
                              have p2289_3 := h2289c.2.2.2
                              linarith only [hlam, p2289_0]
                          · linarith only [h2091, h2288, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1658, h2090, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1658, h2081, h2084, h2089, hc01, hc12, hlam, hphi]
              · linarith only [h0, h2082, h2083, h2088, hc24, hlam, hphi, ht45, u5elo0]
            · linarith only [h0, h2082, h2087, hlam]
          · linarith only [h0, h2081, h2086, hlam]
        · linarith only [h2084, h2085, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2401 | h2401
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2402 | h2402
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2403 | h2403
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2404 | h2404
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2405 | h2405
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2406 | h2406
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2407 | h2407
                    · linarith only [h2081, h2084, h2407, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2409 | h2409
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2410 | h2410
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2411 | h2411
                          · rcases h2bigk with h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c | h2412c
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h0, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2409, h2411, hc02, hc45, hlam, hphi, ht0b, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h0, h2407, h2409, h2411, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              rcases p2412_3 (m.d 0 2) (by simp) with h2417 | h2417
                              · rcases p2412_3 (m.d 1 2) (by simp) with h2418 | h2418
                                · rcases p2412_3 (m.d 2 3) (by simp) with h2419 | h2419
                                  · linarith only [h2081, h2419, hlam]
                                  · linarith only [h2409, h2419, hlam]
                                · linarith only [h2404, h2418, hlam]
                              · linarith only [h2417, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2409, h2411, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2407, h2409, h2411, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              rcases p2412_3 (m.d 0 2) (by simp) with h2428 | h2428
                              · linarith only [h0, h2428, hlam]
                              · linarith only [h2083, h2428, hlam]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2081, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2402, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2407, hlam, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2082, h2407, h2409, h2411, hc02, hc45, hlam, hphi, ht0b, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2082, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2403, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2082, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2082, h2084, h2405, h2409, h2411, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2083, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2404, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2409, hlam, p2412_0]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [h2410, hlam, p2412_1]
                            · have p2412_0 := h2412c.1
                              have p2412_1 := h2412c.2.1
                              have p2412_2 := h2412c.2.2.1
                              have p2412_3 := h2412c.2.2.2
                              linarith only [hlam, p2412_0]
                          · linarith only [h2081, h2084, h2409, h2411, hc35, hlam, hphi, u5elo4]
                        · linarith only [h2407, h2409, h2410, hc35, hlam, hphi, u5elo4]
                      · linarith only [h2084, h2401, h2409, hc23, hc34, hlam, hphi]
                  · linarith only [h2084, h2401, h2405, h2406, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2450 | h2450
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2451 | h2451
                    · linarith only [h1658, h2405, h2451, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2453 | h2453
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2454 | h2454
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2455 | h2455
                          · rcases h2bigk with h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h0, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h0, h2453, h2455, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h0, h2451, h2453, h2455, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              rcases p2456_3 (m.d 0 2) (by simp) with h2461 | h2461
                              · rcases p2456_3 (m.d 1 2) (by simp) with h2462 | h2462
                                · rcases p2456_3 (m.d 2 3) (by simp) with h2463 | h2463
                                  · linarith only [h2081, h2463, hlam]
                                  · linarith only [h2453, h2463, hlam]
                                · linarith only [h2404, h2462, hlam]
                              · linarith only [h2461, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2453, h2455, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2451, h2453, h2455, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              rcases p2456_3 (m.d 0 2) (by simp) with h2472 | h2472
                              · linarith only [h0, h2472, hlam]
                              · linarith only [h2083, h2472, hlam]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2081, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2402, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2451, hlam, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2082, h2451, h2453, h2455, hc02, hc45, hlam, hphi, ht0b, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2082, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2403, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2082, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h0, h2082, h2453, h2455, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2083, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2404, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2453, hlam, p2456_0]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [h2454, hlam, p2456_1]
                            · have p2456_0 := h2456c.1
                              have p2456_1 := h2456c.2.1
                              have p2456_2 := h2456c.2.2.1
                              have p2456_3 := h2456c.2.2.2
                              linarith only [hlam, p2456_0]
                          · linarith only [h1658, h2405, h2455, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h2451, h2453, h2454, hc35, hlam, hphi, u5elo4]
                      · linarith only [h1658, h2401, h2405, h2453, hc23, hc34, hlam, hphi]
                  · linarith only [h1658, h2401, h2450, hlam]
              · linarith only [h0, h2083, h2404, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h0, h2082, h2403, hlam]
          · linarith only [h0, h2081, h2402, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2497 | h2497
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2498 | h2498
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2499 | h2499
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2500 | h2500
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2501 | h2501
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2502 | h2502
                    · linarith only [h0, h1658, h2081, h2084, h2502, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2504 | h2504
                      · linarith only [h2081, h2401, h2504, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2506 | h2506
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2507 | h2507
                          · rcases h2bigk with h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h0, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              rcases p2508_3 (m.d 0 2) (by simp) with h2511 | h2511
                              · rcases p2508_3 (m.d 1 2) (by simp) with h2512 | h2512
                                · rcases p2508_3 (m.d 2 3) (by simp) with h2513 | h2513
                                  · linarith only [h2513, hlam, p2508_0]
                                  · rcases p2508_3 (m.d 2 4) (by simp) with h2515 | h2515
                                    · linarith only [h2082, h2515, hlam]
                                    · linarith only [h2502, h2515, hlam]
                                · linarith only [h2497, h2512, hlam]
                              · linarith only [h2511, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h0, h2506, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2508_1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              rcases p2508_3 (m.d 0 2) (by simp) with h2521 | h2521
                              · rcases p2508_3 (m.d 1 2) (by simp) with h2522 | h2522
                                · rcases p2508_3 (m.d 2 3) (by simp) with h2523 | h2523
                                  · linarith only [h2081, h2523, hlam]
                                  · rcases p2508_3 (m.d 2 4) (by simp) with h2525 | h2525
                                    · linarith only [h2082, h2525, hlam]
                                    · linarith only [h2506, h2525, hlam]
                                · linarith only [h2499, h2522, hlam]
                              · linarith only [h2521, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2508_1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              rcases p2508_3 (m.d 0 2) (by simp) with h2532 | h2532
                              · linarith only [h0, h2532, hlam]
                              · linarith only [h2081, h2532, hlam]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h1658, h2401, h2501, h2506, hc01, hc12, hc45, hlam, hphi, p2508_1, u5elo1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              rcases p2508_3 (m.d 0 2) (by simp) with h2536 | h2536
                              · linarith only [h0, h2536, hlam]
                              · linarith only [h2083, h2536, hlam]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2081, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2497, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2502, hlam, p2508_1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2504, hlam, p2508_1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2082, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2498, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2082, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2508_1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h1658, h2082, h2084, h2401, h2497, h2500, h2501, h2504, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p2508_1, u5elo1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2083, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2499, hlam, p2508_0]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, ht45, p2508_1, u5elo2]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [h2506, hlam, p2508_1]
                            · have p2508_0 := h2508c.1
                              have p2508_1 := h2508c.2.1
                              have p2508_2 := h2508c.2.2.1
                              have p2508_3 := h2508c.2.2.2
                              linarith only [hlam, p2508_0]
                          · linarith only [h1658, h2084, h2507, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2555 | h2555
                          · rcases h2bigk with h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c | h2556c
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h0, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              rcases p2556_3 (m.d 0 2) (by simp) with h2559 | h2559
                              · rcases p2556_3 (m.d 1 2) (by simp) with h2560 | h2560
                                · rcases p2556_3 (m.d 2 3) (by simp) with h2561 | h2561
                                  · linarith only [h2561, hlam, p2556_0]
                                  · rcases p2556_3 (m.d 2 4) (by simp) with h2563 | h2563
                                    · linarith only [h2082, h2563, hlam]
                                    · linarith only [h2502, h2563, hlam]
                                · linarith only [h2497, h2560, hlam]
                              · linarith only [h2559, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              rcases p2556_3 (m.d 0 2) (by simp) with h2568 | h2568
                              · rcases p2556_3 (m.d 1 2) (by simp) with h2569 | h2569
                                · rcases p2556_3 (m.d 2 3) (by simp) with h2570 | h2570
                                  · linarith only [h2081, h2570, hlam]
                                  · rcases p2556_3 (m.d 2 4) (by simp) with h2572 | h2572
                                    · linarith only [h2572, hlam, p2556_0]
                                    · rcases p2556_3 (m.d 2 5) (by simp) with h2574 | h2574
                                      · linarith only [h2083, h2574, hlam]
                                      · linarith only [h2506, h2574, hlam]
                                · linarith only [h2498, h2569, hlam]
                              · linarith only [h2568, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              rcases p2556_3 (m.d 0 2) (by simp) with h2579 | h2579
                              · rcases p2556_3 (m.d 1 2) (by simp) with h2580 | h2580
                                · rcases p2556_3 (m.d 2 3) (by simp) with h2581 | h2581
                                  · linarith only [h2081, h2581, hlam]
                                  · rcases p2556_3 (m.d 2 4) (by simp) with h2583 | h2583
                                    · linarith only [h2082, h2583, hlam]
                                    · rcases p2556_3 (m.d 2 5) (by simp) with h2585 | h2585
                                      · linarith only [h2585, hlam, p2556_0]
                                      · rcases h3bigk with h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h1658, hlam, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2401, hc23, hc35, hlam, hphi, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2084, hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2401, hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          rcases p2587_3 (m.d 0 3) (by simp) with h2593 | h2593
                                          · linarith only [h1658, h2593, hlam]
                                          · rcases p2587_3 (m.d 1 3) (by simp) with h2595 | h2595
                                            · rcases p2587_3 (m.d 2 3) (by simp) with h2596 | h2596
                                              · linarith only [h2497, h2596, hlam]
                                              · rcases p2587_3 (m.d 3 4) (by simp) with h2598 | h2598
                                                · linarith only [h2500, h2598, hlam]
                                                · linarith only [h2084, h2598, hlam]
                                            · linarith only [h1658, h2595, hlam]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2500, h2502, h2506, h2555, hlam, p2587_2]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2502, h2506, h2555, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h1658, h2401, h2497, hc01, hc12, hlam, hphi, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2081, hlam, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2497, hlam, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2502, hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2504, hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h1658, h2497, h2500, hc01, hc12, hlam, hphi, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2500, hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          rcases p2587_3 (m.d 0 3) (by simp) with h2613 | h2613
                                          · linarith only [h2084, h2613, hlam]
                                          · linarith only [h2081, h2613, hlam]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h1658, h2401, h2497, h2500, hc01, hc12, hlam, hphi, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h1658, h2501, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2587_1, u5elo1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2501, hlam, p2587_0]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2501, hc23, hlam, hphi, ht34, ht45, p2587_1, u5elo1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [h2555, hlam, p2587_1]
                                        · have p2587_0 := h2587c.1
                                          have p2587_1 := h2587c.2.1
                                          have p2587_2 := h2587c.2.2.1
                                          have p2587_3 := h2587c.2.2.2
                                          linarith only [hlam, p2587_0]
                                · linarith only [h2499, h2580, hlam]
                              · linarith only [h2579, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2556_1]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              rcases p2556_3 (m.d 0 2) (by simp) with h2627 | h2627
                              · linarith only [h0, h2627, hlam]
                              · linarith only [h2081, h2627, hlam]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              rcases p2556_3 (m.d 0 2) (by simp) with h2630 | h2630
                              · linarith only [h0, h2630, hlam]
                              · linarith only [h2082, h2630, hlam]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              rcases p2556_3 (m.d 0 2) (by simp) with h2633 | h2633
                              · linarith only [h0, h2633, hlam]
                              · linarith only [h2083, h2633, hlam]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2081, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2497, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2502, hlam, p2556_1]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2504, hlam, p2556_1]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2082, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2498, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2083, h2506, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2556_1]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2506, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2083, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2499, hlam, p2556_0]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2083, h2401, h2501, hc23, hlam, hphi, ht34, ht45, p2556_1, u5elo1]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [h2083, h2401, h2501, hc24, hlam, hphi, ht45, p2556_1, u5elo1]
                            · have p2556_0 := h2556c.1
                              have p2556_1 := h2556c.2.1
                              have p2556_2 := h2556c.2.2.1
                              have p2556_3 := h2556c.2.2.2
                              linarith only [hlam, p2556_0]
                          · linarith only [h1658, h2084, h2555, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1658, h2501, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2653 | h2653
                  · linarith only [h1658, h2401, h2500, h2653, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1658, h2653, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2083, h2499, hlam]
            · linarith only [h0, h2082, h2498, hlam]
          · linarith only [h0, h2081, h2497, hlam]
    · linarith only [h2081, h2083, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2660 | h2660
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2661 | h2661
      · linarith only [h2081, h2082, h2661, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2663 | h2663
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2664 | h2664
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2665 | h2665
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2666 | h2666
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2667 | h2667
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2668 | h2668
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2669 | h2669
                    · linarith only [h2081, h2082, h2661, h2665, h2669, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2671 | h2671
                      · linarith only [h2081, h2082, h2664, h2667, h2669, h2671, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2081, h2082, h2663, h2664, h2667, h2669, h2671, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2661, h2663, h2667, h2668, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2675 | h2675
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2676 | h2676
                    · linarith only [h1658, h2667, h2676, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2678 | h2678
                      · linarith only [h2081, h2082, h2665, h2678, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2081, h2082, h2663, h2665, h2678, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1658, h2081, h2082, h2663, h2665, h2675, hc01, hc12, hlam, hphi]
              · linarith only [h2082, h2660, h2665, h2666, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2683 | h2683
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2684 | h2684
                · linarith only [h2661, h2663, h2664, h2665, h2684, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2686 | h2686
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2687 | h2687
                    · linarith only [h0, h2081, h2665, h2684, h2687, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2689 | h2689
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2690 | h2690
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2691 | h2691
                          · rcases h2bigk with h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, h2665, h2687, h2689, h2691, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2082, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, h2665, h2687, h2689, h2691, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2665, h2687, hc02, hc34, hlam, hphi, ht23, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2665, h2687, h2689, h2691, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2665, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2665, h2687, h2689, h2691, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2081, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2664, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2687, hlam, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2081, h2689, h2691, hc02, hc45, hlam, hphi, ht0b, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2687, hc02, hc34, hlam, hphi, ht23, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2687, hc12, hc34, hlam, hphi, ht23, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2687, hc23, hc34, hlam, hphi, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              rcases p2692_3 (m.d 0 2) (by simp) with h2712 | h2712
                              · linarith only [h2082, h2712, hlam]
                              · linarith only [h2660, h2712, hlam]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2660, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2683, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2689, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2690, hlam, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                          · linarith only [h2081, h2082, h2687, h2689, h2691, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h2081, h2665, h2689, h2690, hc35, hlam, hphi, u5elo4]
                      · linarith only [h0, h2081, h2663, h2665, h2687, h2689, hc23, hc34, hlam, hphi]
                  · linarith only [h1658, h2663, h2686, hlam]
              · linarith only [h0, h2660, h2683, hlam]
          · linarith only [h0, h2081, h2664, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2726 | h2726
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2727 | h2727
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2728 | h2728
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2729 | h2729
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2730 | h2730
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2731 | h2731
                    · linarith only [h0, h1658, h2081, h2661, h2731, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2733 | h2733
                      · linarith only [h1658, h2081, h2082, h2663, h2726, h2729, h2731, h2733, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2735 | h2735
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2736 | h2736
                          · rcases h2bigk with h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c | h2737c
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h0, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h1658, h2082, h2663, h2726, h2729, h2730, h2731, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p2737_1, u5elo1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2082, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h1658, h2082, h2663, h2726, h2729, h2730, h2731, hc01, hc12, hc25, hlam, hphi, p2737_1, u5elo1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p2737_1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              rcases p2737_3 (m.d 0 2) (by simp) with h2745 | h2745
                              · linarith only [h0, h2745, hlam]
                              · linarith only [h2081, h2745, hlam]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h1658, h2082, h2660, h2663, h2730, h2733, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p2737_1, u5elo1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              rcases p2737_3 (m.d 0 2) (by simp) with h2749 | h2749
                              · linarith only [h0, h2749, hlam]
                              · linarith only [h2660, h2749, hlam]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2081, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2726, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2731, hlam, p2737_1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2733, hlam, p2737_1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h1658, h2660, h2663, h2730, h2733, hc01, hc23, hc24, hlam, hphi, ht12, ht34, ht45, p2737_1, u5elo1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2727, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h1658, h2663, h2726, h2729, h2730, h2731, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p2737_1, u5elo1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h1658, h2663, h2726, h2729, h2730, h2731, h2733, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p2737_1, u5elo1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2660, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2728, hlam, p2737_0]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2660, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2737_1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [h2735, hlam, p2737_1]
                            · have p2737_0 := h2737c.1
                              have p2737_1 := h2737c.2.1
                              have p2737_2 := h2737c.2.2.1
                              have p2737_3 := h2737c.2.2.2
                              linarith only [hlam, p2737_0]
                          · linarith only [h2082, h2731, h2736, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h2082, h2660, h2733, h2735, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1658, h2730, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2770 | h2770
                  · linarith only [h2663, h2729, h2770, hc03, hc34, hlam, hphi]
                  · linarith only [h1658, h2770, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h2082, h2660, h2728, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2774 | h2774
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2775 | h2775
                · linarith only [h1658, h2661, h2726, h2727, h2775, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2777 | h2777
                  · linarith only [h1658, h2663, h2775, h2777, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1658, h2777, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2774, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h2081, h2663, h2726, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h2081, h2660, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
