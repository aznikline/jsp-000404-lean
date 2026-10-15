import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2080 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2081 | h2081
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2082 | h2082
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2083 | h2083
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2084 | h2084
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2085 | h2085
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2086 | h2086
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2087 | h2087
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2088 | h2088
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2089 | h2089
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2090 | h2090
                    · linarith only [h0, h2080, h2090, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2080, h2086, h2089, h2090, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2089, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2094 | h2094
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2095 | h2095
                    · linarith only [h0, h2080, h2095, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2080, h2086, h2095, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2094, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2099 | h2099
                · linarith only [h2086, h2087, h2099, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2101 | h2101
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2102 | h2102
                    · linarith only [h0, h2080, h2102, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h2086, h2087, h2101, h2102, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h2101, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2106 | h2106
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2107 | h2107
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2108 | h2108
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2109 | h2109
                    · linarith only [h0, h2080, h2086, h2109, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2111 | h2111
                      · linarith only [h0, h2081, h2109, h2111, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h2086, h2106, h2108, h2111, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h2108, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2086, h2106, h2107, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2116 | h2116
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2117 | h2117
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2118 | h2118
                    · linarith only [h0, h2080, h2086, h2118, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2120 | h2120
                      · linarith only [h0, h2080, h2085, h2106, h2120, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2122 | h2122
                        · linarith only [h0, h2081, h2122, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h2081, h2116, h2118, h2122, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2117, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2126 | h2126
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2127 | h2127
                    · linarith only [h2080, h2086, h2127, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2129 | h2129
                      · linarith only [h2080, h2106, h2129, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2131 | h2131
                        · linarith only [h0, h2081, h2116, h2131, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2133 | h2133
                          · linarith only [h2080, h2086, h2126, h2133, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2135 | h2135
                            · linarith only [h2080, h2106, h2126, h2135, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2137 | h2137
                              · rcases h0bigk with h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c | h2138c
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, hlam, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2080, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2081, h2116, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2080, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2081, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2084, h2116, h2133, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2080, hlam, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2083, hlam, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2086, hlam, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2106, hlam, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2081, hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2084, hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2080, h2116, h2126, h2137, hc23, hc34, hlam, hphi, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2116, hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2082, hlam, p2138_0]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h2085, hlam, p2138_1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2080, h2082, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [h0, h2082, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2138_1, u2elo1]
                                · have p2138_0 := h2138c.1
                                  have p2138_1 := h2138c.2.1
                                  have p2138_2 := h2138c.2.2.1
                                  have p2138_3 := h2138c.2.2.2
                                  linarith only [hlam, p2138_0]
                              · rcases h0bigk with h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, hlam, p2164_1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2080, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2080, h2086, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2080, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2080, h2086, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2082, h2126, h2127, h2131, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2080, hlam, p2164_1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2083, hlam, p2164_1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2086, hlam, p2164_1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2106, hlam, p2164_1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2081, hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2084, hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2080, h2081, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2116, hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2082, hlam, p2164_0]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h2085, hlam, p2164_1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2080, h2082, h2126, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [h0, h2082, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2164_1, u2elo1]
                                · have p2164_0 := h2164c.1
                                  have p2164_1 := h2164c.2.1
                                  have p2164_2 := h2164c.2.2.1
                                  have p2164_3 := h2164c.2.2.2
                                  linarith only [hlam, p2164_0]
                  · linarith only [h0, h2126, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h0, h2082, h2085, hlam]
        · linarith only [h0, h2081, h2084, hlam]
      · linarith only [h0, h2080, h2083, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2194 | h2194
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2195 | h2195
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2196 | h2196
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2197 | h2197
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2198 | h2198
              · linarith only [h2080, h2082, h2198, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2200 | h2200
                · linarith only [h2080, h2082, h2197, h2200, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2202 | h2202
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2203 | h2203
                    · linarith only [h0, h2080, h2203, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2080, h2197, h2202, h2203, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2202, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2207 | h2207
              · linarith only [h2081, h2082, h2197, h2207, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2209 | h2209
                · linarith only [h2081, h2082, h2209, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2211 | h2211
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2212 | h2212
                    · linarith only [h0, h2080, h2197, h2212, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2214 | h2214
                      · linarith only [h0, h2080, h2207, h2214, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2216 | h2216
                        · linarith only [h0, h2081, h2216, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2218 | h2218
                          · linarith only [h2194, h2197, h2218, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2220 | h2220
                            · linarith only [h2082, h2214, h2220, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2222 | h2222
                              · linarith only [h2081, h2082, h2211, h2212, h2216, h2222, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2082, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2081, h2211, h2212, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2080, h2211, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2081, h2211, h2212, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2081, h2082, h2211, h2212, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2080, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2194, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2197, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2207, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2081, hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2195, hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2080, h2081, h2211, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2209, hlam, p2224_0]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2080, h2211, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h2196, hlam, p2224_1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2080, h2196, h2211, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [h0, h2196, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2224_1, u2elo1]
                                · have p2224_0 := h2224c.1
                                  have p2224_1 := h2224c.2.1
                                  have p2224_2 := h2224c.2.2.1
                                  have p2224_3 := h2224c.2.2.2
                                  linarith only [hlam, p2224_0]
                  · linarith only [h0, h2080, h2211, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2251 | h2251
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2252 | h2252
              · linarith only [h0, h2080, h2196, h2252, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2254 | h2254
                · linarith only [h0, h2081, h2196, h2254, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2256 | h2256
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2257 | h2257
                    · linarith only [h0, h2080, h2196, h2257, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h0, h2080, h2196, h2251, h2257, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h2256, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2261 | h2261
              · linarith only [h0, h2081, h2196, h2251, h2261, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2263 | h2263
                · linarith only [h0, h2081, h2196, h2263, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2265 | h2265
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2266 | h2266
                    · linarith only [h0, h2080, h2251, h2266, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2268 | h2268
                      · linarith only [h0, h2080, h2196, h2261, h2268, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2270 | h2270
                        · linarith only [h0, h2081, h2196, h2270, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2272 | h2272
                          · linarith only [h2194, h2196, h2251, h2272, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2274 | h2274
                            · linarith only [h2081, h2082, h2265, h2266, h2268, h2274, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2276 | h2276
                              · linarith only [h2081, h2082, h2266, h2270, h2276, hc13, hc34, hlam, hphi]
                              · rcases h0bigk with h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c | h2278c
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h0, hlam, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h0, h2196, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h0, h2196, h2251, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2082, hlam, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2196, hc01, hlam, hphi, ht12, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2080, h2196, h2265, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2080, h2196, h2251, h2265, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2196, hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2080, hlam, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2194, hlam, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2251, hlam, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2261, hlam, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2081, hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2195, hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2080, h2081, h2082, h2265, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2263, hlam, p2278_0]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2080, h2265, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2278_1]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2196, hc02, hlam, hphi, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2080, h2196, h2265, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [h2196, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2278_1, u2elo4]
                                · have p2278_0 := h2278c.1
                                  have p2278_1 := h2278c.2.1
                                  have p2278_2 := h2278c.2.2.1
                                  have p2278_3 := h2278c.2.2.2
                                  linarith only [hlam, p2278_0]
                  · linarith only [h0, h2265, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h0, h2081, h2195, hlam]
      · linarith only [h0, h2080, h2194, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2307 | h2307
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2308 | h2308
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2309 | h2309
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2310 | h2310
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2311 | h2311
            · linarith only [h2080, h2081, h2311, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2313 | h2313
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2314 | h2314
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2315 | h2315
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2316 | h2316
                    · linarith only [h0, h2080, h2311, h2316, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2318 | h2318
                      · linarith only [h0, h2080, h2318, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h2080, h2313, h2315, h2318, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2315, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2080, h2081, h2313, h2314, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2323 | h2323
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2324 | h2324
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2325 | h2325
                    · linarith only [h0, h2080, h2311, h2325, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2327 | h2327
                      · linarith only [h0, h2080, h2310, h2313, h2327, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2329 | h2329
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2330 | h2330
                          · linarith only [h2081, h2325, h2330, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2332 | h2332
                            · linarith only [h2081, h2307, h2313, h2324, h2327, h2332, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2334 | h2334
                              · rcases h0bigk with h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [hlam, p2335_0]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2081, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [hlam, p2335_0]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, h2080, h2324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, h2080, h2081, h2324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, h2307, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2080, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2308, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [hlam, p2335_0]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2311, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2313, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2080, h2324, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2309, hlam, p2335_0]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2080, h2081, h2324, h2325, hc23, hc34, hlam, hphi, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [hlam, p2335_0]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, h2080, h2309, h2313, h2324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2307, hlam, p2335_0]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2310, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h0, h2080, h2307, h2324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2335_1, u2elo1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [h2323, hlam, p2335_1]
                                · have p2335_0 := h2335c.1
                                  have p2335_1 := h2335c.2.1
                                  have p2335_2 := h2335c.2.2.1
                                  have p2335_3 := h2335c.2.2.2
                                  linarith only [hlam, p2335_0]
                              · linarith only [h2080, h2081, h2324, h2325, h2334, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h2081, h2307, h2313, h2323, h2324, h2327, h2329, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h2324, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2081, h2307, h2323, hlam]
          · linarith only [h0, h2307, h2310, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2366 | h2366
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2367 | h2367
            · linarith only [h0, h2080, h2309, h2367, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2369 | h2369
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2370 | h2370
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2371 | h2371
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2372 | h2372
                    · linarith only [h0, h2080, h2367, h2372, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2374 | h2374
                      · linarith only [h0, h2080, h2309, h2374, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h0, h2080, h2309, h2369, h2371, h2374, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2371, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h2080, h2309, h2369, h2370, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2379 | h2379
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2380 | h2380
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2381 | h2381
                    · linarith only [h0, h2080, h2367, h2381, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2383 | h2383
                      · linarith only [h0, h2080, h2309, h2369, h2383, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2385 | h2385
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2386 | h2386
                          · linarith only [h2081, h2381, h2386, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2388 | h2388
                            · linarith only [h2080, h2369, h2380, h2388, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2390 | h2390
                              · rcases h0bigk with h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [hlam, p2391_0]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h0, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2080, h2081, h2380, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2081, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h0, h2080, h2309, h2369, h2380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2309, hc01, hlam, hphi, ht12, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [hlam, p2391_0]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2080, h2309, h2380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2309, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2080, h2309, h2369, h2380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2080, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2308, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [hlam, p2391_0]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2367, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2369, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2307, h2380, h2383, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2309, hc02, hlam, hphi, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2080, h2309, h2380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [hlam, p2391_0]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2080, h2309, h2369, h2380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2391_1, u2elo3]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2307, hlam, p2391_0]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2366, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h0, h2080, h2307, h2380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2391_1, u2elo0]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [h2379, hlam, p2391_1]
                                · have p2391_0 := h2391c.1
                                  have p2391_1 := h2391c.2.1
                                  have p2391_2 := h2391c.2.2.1
                                  have p2391_3 := h2391c.2.2.2
                                  linarith only [hlam, p2391_0]
                              · linarith only [h0, h2080, h2309, h2380, h2386, h2390, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h2081, h2307, h2380, h2383, h2385, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2380, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2081, h2307, h2379, hlam]
          · linarith only [h0, h2307, h2366, hlam]
      · linarith only [h0, h2080, h2308, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2423 | h2423
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2424 | h2424
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2425 | h2425
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2426 | h2426
            · linarith only [h2080, h2081, h2426, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2428 | h2428
              · linarith only [h2080, h2307, h2428, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2430 | h2430
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2431 | h2431
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2432 | h2432
                    · linarith only [h0, h2080, h2426, h2432, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2434 | h2434
                      · linarith only [h0, h2080, h2428, h2434, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2436 | h2436
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2437 | h2437
                          · linarith only [h2307, h2432, h2436, h2437, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2439 | h2439
                            · linarith only [h2080, h2307, h2431, h2434, h2439, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2441 | h2441
                              · rcases h0bigk with h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [hlam, p2442_0]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, h2080, h2431, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2081, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2307, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [hlam, p2442_0]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, h2080, h2431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, h2307, hc01, hlam, hphi, ht12, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2080, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2423, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [hlam, p2442_0]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2426, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2428, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2080, h2431, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2424, hlam, p2442_0]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, h2080, h2424, h2431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [hlam, p2442_0]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, h2080, h2307, h2424, h2431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2080, h2431, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2425, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h0, h2080, h2425, h2431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2442_1, u2elo1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [h2430, hlam, p2442_1]
                                · have p2442_0 := h2442c.1
                                  have p2442_1 := h2442c.2.1
                                  have p2442_2 := h2442c.2.2.1
                                  have p2442_3 := h2442c.2.2.2
                                  linarith only [hlam, p2442_0]
                              · linarith only [h2080, h2081, h2431, h2432, h2441, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h2081, h2430, h2436, hlam]
                  · linarith only [h0, h2431, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2471 | h2471
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2472 | h2472
                    · linarith only [h2080, h2081, h2430, h2472, hc34, hc45, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2474 | h2474
                      · linarith only [h0, h2080, h2474, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2476 | h2476
                        · linarith only [h2080, h2081, h2430, h2471, h2472, h2476, hc23, hc34, hlam, hphi]
                        · linarith only [h2080, h2081, h2471, h2476, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2471, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2480 | h2480
            · linarith only [h2080, h2081, h2480, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2482 | h2482
              · linarith only [h2080, h2081, h2424, h2425, h2482, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2484 | h2484
                · linarith only [h2424, h2425, h2484, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2486 | h2486
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2487 | h2487
                    · linarith only [h2080, h2081, h2424, h2425, h2480, h2487, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2489 | h2489
                      · linarith only [h2080, h2081, h2424, h2425, h2482, h2489, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2491 | h2491
                        · linarith only [h2080, h2081, h2484, h2487, h2491, hc13, hc34, hlam, hphi]
                        · linarith only [h2080, h2081, h2486, h2491, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2080, h2486, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2495 | h2495
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2496 | h2496
            · linarith only [h0, h2080, h2424, h2496, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2498 | h2498
              · linarith only [h2080, h2307, h2498, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2500 | h2500
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2501 | h2501
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2502 | h2502
                    · linarith only [h0, h2080, h2496, h2502, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2504 | h2504
                      · linarith only [h2080, h2307, h2498, h2504, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2506 | h2506
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2507 | h2507
                          · linarith only [h2307, h2502, h2506, h2507, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2509 | h2509
                            · linarith only [h2080, h2307, h2501, h2504, h2509, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2511 | h2511
                              · rcases h0bigk with h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [hlam, p2512_0]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h0, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h0, h2080, h2501, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2081, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2307, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2424, hc01, hlam, hphi, ht12, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [hlam, p2512_0]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, h2424, h2501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2424, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2424, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2423, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [hlam, p2512_0]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2496, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2498, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, h2501, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2424, hc02, hlam, hphi, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, h2424, h2501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [hlam, p2512_0]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, h2307, h2424, h2501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, h2495, h2501, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2495, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2080, h2424, h2495, h2501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2512_1, u2elo3]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [h2500, hlam, p2512_1]
                                · have p2512_0 := h2512c.1
                                  have p2512_1 := h2512c.2.1
                                  have p2512_2 := h2512c.2.2.1
                                  have p2512_3 := h2512c.2.2.2
                                  linarith only [hlam, p2512_0]
                              · linarith only [h2424, h2495, h2500, h2507, h2511, hlam]
                        · linarith only [h2080, h2081, h2424, h2495, h2500, h2501, h2506, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2501, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2424, h2495, h2500, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2542 | h2542
            · linarith only [h0, h2080, h2424, h2542, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2544 | h2544
              · linarith only [h0, h2080, h2495, h2544, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2546 | h2546
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2547 | h2547
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2548 | h2548
                    · linarith only [h2080, h2081, h2542, h2548, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2550 | h2550
                      · linarith only [h0, h2080, h2495, h2544, h2550, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2552 | h2552
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2553 | h2553
                          · linarith only [h2081, h2548, h2553, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2555 | h2555
                            · linarith only [h2080, h2307, h2547, h2550, h2555, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2557 | h2557
                              · rcases h0bigk with h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [hlam, p2558_0]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h0, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, h2307, h2547, h2552, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2081, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2307, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2495, hc01, hlam, hphi, ht12, p2558_1, u2elo4]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [hlam, p2558_0]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, h2495, h2547, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2558_1, u2elo4]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2424, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2495, hlam, p2558_0]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2423, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [hlam, p2558_0]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2542, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2544, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, h2547, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2424, hc02, hlam, hphi, p2558_1, u2elo3]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, h2424, h2547, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2558_1, u2elo3]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [hlam, p2558_0]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h0, h2080, h2424, h2495, h2547, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2558_1, u2elo3]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, h2547, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h0, h2080, h2495, h2547, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2558_1, u2elo4]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2080, h2495, h2547, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2558_1, u2elo4]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [h2546, hlam, p2558_1]
                                · have p2558_0 := h2558c.1
                                  have p2558_1 := h2558c.2.1
                                  have p2558_2 := h2558c.2.2.1
                                  have p2558_3 := h2558c.2.2.2
                                  linarith only [hlam, p2558_0]
                              · linarith only [h2080, h2081, h2424, h2546, h2547, h2548, h2557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · linarith only [h2081, h2546, h2552, hlam]
                  · linarith only [h0, h2547, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2587 | h2587
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2588 | h2588
                    · linarith only [h0, h2080, h2588, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2590 | h2590
                      · linarith only [h0, h2080, h2424, h2590, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2592 | h2592
                        · linarith only [h2080, h2081, h2546, h2587, h2588, h2592, hc23, hc34, hlam, hphi]
                        · linarith only [h2080, h2081, h2587, h2592, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2080, h2587, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h2080, h2423, hlam]

end R2N4
