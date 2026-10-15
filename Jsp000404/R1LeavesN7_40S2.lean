import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1489 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1490 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1491 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h2091 | h2091
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2092 | h2092
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2093 | h2093
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2094 | h2094
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2095 | h2095
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2096 | h2096
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2097 | h2097
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2098 | h2098
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
                  · linarith only [h1487, h1491, h2099, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2101 | h2101
                    · linarith only [h1486, h1487, h1491, h2097, h2101, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases h1bigk with h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h0, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h927, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1487, h1491, h2096, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1241, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 1) (by simp) with h2109 | h2109
                        · linarith only [h2109, hlam, p2103_0]
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2111 | h2111
                          · rcases p2103_3 (m.d 1 3) (by simp) with h2112 | h2112
                            · linarith only [h2091, h2112, hlam]
                            · linarith only [h2112, h927, hlam]
                          · linarith only [h2111, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p2103_1]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1487, h1491, h2096, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1241, hc01, hc12, hlam, hphi, p2103_1]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 1) (by simp) with h2120 | h2120
                        · linarith only [h2120, hlam, p2103_0]
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2122 | h2122
                          · rcases p2103_3 (m.d 1 3) (by simp) with h2123 | h2123
                            · rcases p2103_3 (m.d 1 4) (by simp) with h2124 | h2124
                              · linarith only [h2094, h2124, hlam]
                              · linarith only [h0, h1487, h1491, h2096, h2124, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h2123, hlam, p2103_0]
                          · linarith only [h0, h2122, hlam]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2091, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1487, h1491, h2096, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1487, h1491, h2091, h2096, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 1) (by simp) with h2133 | h2133
                        · linarith only [h2133, hlam, p2103_0]
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2135 | h2135
                          · rcases p2103_3 (m.d 1 3) (by simp) with h2136 | h2136
                            · rcases p2103_3 (m.d 1 4) (by simp) with h2137 | h2137
                              · rcases p2103_3 (m.d 1 5) (by simp) with h2138 | h2138
                                · linarith only [h2096, h2138, hlam]
                                · linarith only [h1241, h2138, hlam]
                              · linarith only [h2137, hlam, p2103_0]
                            · linarith only [h2136, h927, hlam]
                          · linarith only [h0, h2135, hlam]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2092, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2094, hlam, p2103_1]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h1487, h1491, h2096, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 1) (by simp) with h2148 | h2148
                        · linarith only [h2148, hlam, p2103_0]
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2150 | h2150
                          · rcases p2103_3 (m.d 1 3) (by simp) with h2151 | h2151
                            · rcases p2103_3 (m.d 1 4) (by simp) with h2152 | h2152
                              · rcases p2103_3 (m.d 1 5) (by simp) with h2153 | h2153
                                · rcases h5bigk with h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1241, hlam, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u2ehi4]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1491, h2091, h2094, h2096, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1491, hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1241, hc01, hc15, hlam, hphi, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2093, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u2ehi4]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    rcases p2154_3 (m.d 0 5) (by simp) with h2163 | h2163
                                    · linarith only [h1241, h2163, hlam]
                                    · linarith only [h1490, h2163, hlam]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1487, h1491, h2091, h2094, h2096, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u2ehi3]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1488, hlam, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2093, hlam, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h0, h1488, h2101, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2099, hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1490, hlam, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2095, hlam, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2098, hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2101, hlam, p2154_0]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h1488, hc45, hlam, hphi, ht23, ht34, p2154_1, u2ehi4]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2096, hlam, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2091, h2094, h2096, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u2ehi4]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [h2091, h2094, h2096, h2101, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2154_1]
                                  · have p2154_0 := h2154c.1
                                    have p2154_1 := h2154c.2.1
                                    have p2154_2 := h2154c.2.2.1
                                    have p2154_3 := h2154c.2.2.2
                                    linarith only [hlam, p2154_0]
                                · linarith only [h2153, hlam, p2103_0]
                              · linarith only [h2096, h2152, hlam, p2103_1]
                            · linarith only [h2151, h927, hlam]
                          · linarith only [h0, h2150, hlam]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2093, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2095, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2096, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2190 | h2190
                  · linarith only [h1490, h1491, h2098, h2190, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2192 | h2192
                    · linarith only [h1490, h1491, h2097, h2098, h2192, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h1bigk with h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h0, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h927, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1241, h1491, h2096, hlam, p2194_1]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1241, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        rcases p2194_3 (m.d 0 1) (by simp) with h2200 | h2200
                        · linarith only [h2200, hlam, p2194_0]
                        · rcases p2194_3 (m.d 1 2) (by simp) with h2202 | h2202
                          · rcases p2194_3 (m.d 1 3) (by simp) with h2203 | h2203
                            · linarith only [h2091, h2203, hlam]
                            · linarith only [h2203, h927, hlam]
                          · linarith only [h2202, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1490, h1491, h2094, h2096, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2194_1, u2ehi3]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1490, h1491, h2096, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2194_1, u2ehi3]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1241, hc01, hc12, hlam, hphi, p2194_1]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        rcases p2194_3 (m.d 0 1) (by simp) with h2211 | h2211
                        · linarith only [h2211, hlam, p2194_0]
                        · rcases p2194_3 (m.d 1 2) (by simp) with h2213 | h2213
                          · rcases p2194_3 (m.d 1 3) (by simp) with h2214 | h2214
                            · rcases p2194_3 (m.d 1 4) (by simp) with h2215 | h2215
                              · linarith only [h2094, h2215, hlam]
                              · linarith only [h0, h1490, h1491, h2096, h2097, h2098, h2215, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h2214, hlam, p2194_0]
                          · linarith only [h0, h2213, hlam]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h2091, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1490, h1491, h2096, h2097, h2098, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2194_1, u2ehi3]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1490, h1491, h2091, h2096, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2194_1, u2ehi3]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        rcases p2194_3 (m.d 0 1) (by simp) with h2224 | h2224
                        · linarith only [h2224, hlam, p2194_0]
                        · rcases p2194_3 (m.d 1 2) (by simp) with h2226 | h2226
                          · rcases p2194_3 (m.d 1 3) (by simp) with h2227 | h2227
                            · rcases p2194_3 (m.d 1 4) (by simp) with h2228 | h2228
                              · rcases p2194_3 (m.d 1 5) (by simp) with h2229 | h2229
                                · linarith only [h2096, h2229, hlam]
                                · linarith only [h1241, h2229, hlam]
                              · linarith only [h2228, hlam, p2194_0]
                            · linarith only [h2227, h927, hlam]
                          · linarith only [h0, h2226, hlam]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h2092, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h2094, hlam, p2194_1]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h1490, h1491, h2096, h2097, h2098, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2194_1, u2ehi3]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        rcases p2194_3 (m.d 0 1) (by simp) with h2239 | h2239
                        · linarith only [h2239, hlam, p2194_0]
                        · rcases p2194_3 (m.d 1 2) (by simp) with h2241 | h2241
                          · rcases p2194_3 (m.d 1 3) (by simp) with h2242 | h2242
                            · rcases p2194_3 (m.d 1 4) (by simp) with h2243 | h2243
                              · rcases p2194_3 (m.d 1 5) (by simp) with h2244 | h2244
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
                                    linarith only [h1241, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2097, h2098, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2097, h2098, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1491, hlam, p2245_0]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1241, hc01, hc15, hlam, hphi, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [hlam, p2245_0]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2093, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2091, h2095, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1491, h2091, h2094, h2096, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1488, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2093, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [hlam, p2245_0]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2098, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2190, hlam, p2245_0]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1490, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2095, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1490, h2097, h2098, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [hlam, p2245_0]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2192, hlam, p2245_0]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h1241, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2096, hlam, p2245_1]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2091, h2094, h2096, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [h2091, h2094, h2096, h2097, h2098, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2245_1, u2ehi3]
                                  · have p2245_0 := h2245c.1
                                    have p2245_1 := h2245c.2.1
                                    have p2245_2 := h2245c.2.2.1
                                    have p2245_3 := h2245c.2.2.2
                                    linarith only [hlam, p2245_0]
                                · linarith only [h2244, hlam, p2194_0]
                              · linarith only [h2096, h2243, hlam, p2194_1]
                            · linarith only [h2242, h927, hlam]
                          · linarith only [h0, h2241, hlam]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h2093, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h2095, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [h2096, hlam, p2194_0]
                      · have p2194_0 := h2194c.1
                        have p2194_1 := h2194c.2.1
                        have p2194_2 := h2194c.2.2.1
                        have p2194_3 := h2194c.2.2.2
                        linarith only [hlam, p2194_0]
              · linarith only [h1489, h1491, h2096, h2097, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2280 | h2280
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2281 | h2281
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2282 | h2282
                  · linarith only [h0, h1241, h1486, h2096, h2280, h2282, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2284 | h2284
                    · linarith only [h0, h1241, h1487, h2096, h2280, h2284, hc01, hc12, hlam, hphi]
                    · rcases h1bigk with h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h0, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h927, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2091, h2092, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2286_1, u2ehi3]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h1241, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        rcases p2286_3 (m.d 0 1) (by simp) with h2292 | h2292
                        · linarith only [h2292, hlam, p2286_0]
                        · rcases p2286_3 (m.d 1 2) (by simp) with h2294 | h2294
                          · rcases p2286_3 (m.d 1 3) (by simp) with h2295 | h2295
                            · linarith only [h2091, h2295, hlam]
                            · linarith only [h2295, h927, hlam]
                          · linarith only [h2294, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p2286_1]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        rcases p2286_3 (m.d 0 1) (by simp) with h2301 | h2301
                        · linarith only [h0, h2301, hlam]
                        · rcases p2286_3 (m.d 1 2) (by simp) with h2303 | h2303
                          · rcases p2286_3 (m.d 1 3) (by simp) with h2304 | h2304
                            · linarith only [h2091, h2304, hlam]
                            · linarith only [h2094, h2304, hlam]
                          · linarith only [h2092, h2303, hlam]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h1241, hc01, hc12, hlam, hphi, p2286_1]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        rcases p2286_3 (m.d 0 1) (by simp) with h2309 | h2309
                        · linarith only [h2309, hlam, p2286_0]
                        · rcases p2286_3 (m.d 1 2) (by simp) with h2311 | h2311
                          · rcases p2286_3 (m.d 1 3) (by simp) with h2312 | h2312
                            · rcases p2286_3 (m.d 1 4) (by simp) with h2313 | h2313
                              · linarith only [h2094, h2313, hlam]
                              · rcases p2286_3 (m.d 1 5) (by simp) with h2315 | h2315
                                · linarith only [h2095, h2315, hlam]
                                · linarith only [h1241, h2315, hlam]
                            · linarith only [h2312, hlam, p2286_0]
                          · linarith only [h0, h2311, hlam]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2091, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        rcases p2286_3 (m.d 0 1) (by simp) with h2322 | h2322
                        · linarith only [h2322, h927, hlam]
                        · rcases p2286_3 (m.d 1 2) (by simp) with h2324 | h2324
                          · rcases p2286_3 (m.d 1 3) (by simp) with h2325 | h2325
                            · rcases p2286_3 (m.d 1 4) (by simp) with h2326 | h2326
                              · linarith only [h2094, h2326, hlam]
                              · rcases p2286_3 (m.d 1 5) (by simp) with h2328 | h2328
                                · linarith only [h2095, h2328, hlam]
                                · linarith only [h2096, h2328, hlam]
                            · linarith only [h2094, h2325, hlam]
                          · linarith only [h2092, h2324, hlam]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h1241, hc01, hc13, hlam, hphi, p2286_1]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2096, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2286_1]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2092, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2094, hlam, p2286_1]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2096, hlam, p2286_1]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        rcases p2286_3 (m.d 0 1) (by simp) with h2339 | h2339
                        · linarith only [h2339, hlam, p2286_0]
                        · rcases p2286_3 (m.d 1 2) (by simp) with h2341 | h2341
                          · rcases p2286_3 (m.d 1 3) (by simp) with h2342 | h2342
                            · rcases p2286_3 (m.d 1 4) (by simp) with h2343 | h2343
                              · linarith only [h2096, h2343, hlam]
                              · linarith only [h2092, h2096, h2343, hc45, hlam, hphi, ht23, ht34, p2286_1, u2ehi3]
                            · linarith only [h2342, h927, hlam]
                          · linarith only [h0, h2341, hlam]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2093, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2095, hlam, p2286_0]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [h2092, h2096, hc45, hlam, hphi, ht23, ht34, p2286_1, u2ehi3]
                      · have p2286_0 := h2286c.1
                        have p2286_1 := h2286c.2.1
                        have p2286_2 := h2286c.2.2.1
                        have p2286_3 := h2286c.2.2.2
                        linarith only [hlam, p2286_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2352 | h2352
                  · linarith only [h1241, h2096, h2280, h2281, h2352, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2354 | h2354
                    · linarith only [h1487, h1491, h2354, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h1bigk with h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h0, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h927, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h0, h2092, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2356_1, u2ehi3]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h1241, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        rcases p2356_3 (m.d 0 1) (by simp) with h2362 | h2362
                        · linarith only [h2362, hlam, p2356_0]
                        · rcases p2356_3 (m.d 1 2) (by simp) with h2364 | h2364
                          · rcases p2356_3 (m.d 1 3) (by simp) with h2365 | h2365
                            · linarith only [h2091, h2365, hlam]
                            · linarith only [h2365, h927, hlam]
                          · linarith only [h2364, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h1490, h2280, h2281, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2356_1, u2ehi3]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        rcases p2356_3 (m.d 0 1) (by simp) with h2371 | h2371
                        · linarith only [h0, h2371, hlam]
                        · rcases p2356_3 (m.d 1 2) (by simp) with h2373 | h2373
                          · rcases p2356_3 (m.d 1 3) (by simp) with h2374 | h2374
                            · linarith only [h2091, h2374, hlam]
                            · linarith only [h2094, h2374, hlam]
                          · linarith only [h2092, h2373, hlam]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h1241, h1490, h2280, h2281, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2356_1, u2ehi3]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        rcases p2356_3 (m.d 0 1) (by simp) with h2379 | h2379
                        · linarith only [h2379, hlam, p2356_0]
                        · rcases p2356_3 (m.d 1 2) (by simp) with h2381 | h2381
                          · rcases p2356_3 (m.d 1 3) (by simp) with h2382 | h2382
                            · rcases p2356_3 (m.d 1 4) (by simp) with h2383 | h2383
                              · linarith only [h2094, h2383, hlam]
                              · rcases p2356_3 (m.d 1 5) (by simp) with h2385 | h2385
                                · linarith only [h2095, h2385, hlam]
                                · linarith only [h1241, h2385, hlam]
                            · linarith only [h2382, hlam, p2356_0]
                          · linarith only [h0, h2381, hlam]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2091, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        rcases p2356_3 (m.d 0 1) (by simp) with h2392 | h2392
                        · linarith only [h2392, h927, hlam]
                        · rcases p2356_3 (m.d 1 2) (by simp) with h2394 | h2394
                          · rcases p2356_3 (m.d 1 3) (by simp) with h2395 | h2395
                            · rcases p2356_3 (m.d 1 4) (by simp) with h2396 | h2396
                              · linarith only [h2094, h2396, hlam]
                              · rcases p2356_3 (m.d 1 5) (by simp) with h2398 | h2398
                                · linarith only [h2095, h2398, hlam]
                                · linarith only [h2096, h2398, hlam]
                            · linarith only [h2094, h2395, hlam]
                          · linarith only [h2092, h2394, hlam]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h1241, h1490, h2280, h2281, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2356_1, u2ehi3]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2096, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2356_1]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2092, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2094, hlam, p2356_1]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2096, hlam, p2356_1]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        rcases p2356_3 (m.d 0 1) (by simp) with h2409 | h2409
                        · linarith only [h2409, hlam, p2356_0]
                        · rcases p2356_3 (m.d 1 2) (by simp) with h2411 | h2411
                          · rcases p2356_3 (m.d 1 3) (by simp) with h2412 | h2412
                            · rcases p2356_3 (m.d 1 4) (by simp) with h2413 | h2413
                              · linarith only [h2096, h2413, hlam]
                              · linarith only [h2092, h2096, h2413, hc45, hlam, hphi, ht23, ht34, p2356_1, u2ehi3]
                            · linarith only [h2412, h927, hlam]
                          · linarith only [h0, h2411, hlam]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2093, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2095, hlam, p2356_0]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [h2092, h2096, hc45, hlam, hphi, ht23, ht34, p2356_1, u2ehi3]
                      · have p2356_0 := h2356c.1
                        have p2356_1 := h2356c.2.1
                        have p2356_2 := h2356c.2.2.1
                        have p2356_3 := h2356c.2.2.2
                        linarith only [hlam, p2356_0]
              · linarith only [h1489, h1491, h2280, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1486, h1490, h2095, h927, hc01, hc12, hlam, hphi]
        · linarith only [h1489, h1491, h2094, h927, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h1486, h2093, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1486, h2092, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h1487, h2091, hc23, hlam, hphi, u2ehi3]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1489 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1490 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h1491 | h1491
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488 h1489 h1490 h1491
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488 h1489 h1490 h1491

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1489 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1490 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h2428 | h2428
  · linarith only [h1489, h1490, h2428, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2430 | h2430
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2431 | h2431
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2432 | h2432
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2433 | h2433
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2434 | h2434
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2435 | h2435
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2436 | h2436
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2437 | h2437
                  · linarith only [h1486, h1490, h2437, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2439 | h2439
                    · linarith only [h1487, h1488, h1489, h1490, h2428, h2430, h2434, h2439, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2441 | h2441
                      · linarith only [h1486, h1490, h2428, h2430, h2434, h2436, h2441, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c | h2443c
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h0, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h927, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1490, h2435, h2441, h927, hlam, p2443_1]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1241, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          rcases p2443_3 (m.d 0 1) (by simp) with h2449 | h2449
                          · linarith only [h2449, hlam, p2443_0]
                          · rcases p2443_3 (m.d 1 2) (by simp) with h2451 | h2451
                            · rcases p2443_3 (m.d 1 3) (by simp) with h2452 | h2452
                              · linarith only [h2430, h2452, hlam]
                              · linarith only [h2452, h927, hlam]
                            · linarith only [h2451, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1490, h2433, h2435, h2441, h927, hc01, hc12, hlam, hphi, p2443_1]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1487, h1489, h1490, h2435, h2441, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2443_1, u2ehi3]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1487, h1489, h1490, h2435, h2441, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2443_1, u2ehi3]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          rcases p2443_3 (m.d 0 1) (by simp) with h2460 | h2460
                          · linarith only [h2460, hlam, p2443_0]
                          · rcases p2443_3 (m.d 1 2) (by simp) with h2462 | h2462
                            · rcases p2443_3 (m.d 1 3) (by simp) with h2463 | h2463
                              · rcases p2443_3 (m.d 1 4) (by simp) with h2464 | h2464
                                · linarith only [h2433, h2464, hlam]
                                · linarith only [h0, h1487, h1489, h1490, h2435, h2441, h2464, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h2463, hlam, p2443_0]
                            · linarith only [h0, h2462, hlam]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h2430, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1487, h1489, h1490, h2435, h2441, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2443_1, u2ehi3]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1487, h1489, h1490, h2430, h2435, h2441, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2443_1, u2ehi3]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          rcases p2443_3 (m.d 0 1) (by simp) with h2473 | h2473
                          · linarith only [h2473, hlam, p2443_0]
                          · rcases p2443_3 (m.d 1 2) (by simp) with h2475 | h2475
                            · rcases p2443_3 (m.d 1 3) (by simp) with h2476 | h2476
                              · rcases p2443_3 (m.d 1 4) (by simp) with h2477 | h2477
                                · rcases p2443_3 (m.d 1 5) (by simp) with h2478 | h2478
                                  · linarith only [h2435, h2478, hlam]
                                  · linarith only [h1241, h2478, hlam]
                                · linarith only [h2477, hlam, p2443_0]
                              · linarith only [h2476, h927, hlam]
                            · linarith only [h0, h2475, hlam]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h2431, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h2433, hlam, p2443_1]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h1487, h1489, h1490, h2435, h2441, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2443_1, u2ehi3]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          rcases p2443_3 (m.d 0 1) (by simp) with h2488 | h2488
                          · linarith only [h2488, hlam, p2443_0]
                          · rcases p2443_3 (m.d 1 2) (by simp) with h2490 | h2490
                            · rcases p2443_3 (m.d 1 3) (by simp) with h2491 | h2491
                              · rcases p2443_3 (m.d 1 4) (by simp) with h2492 | h2492
                                · rcases p2443_3 (m.d 1 5) (by simp) with h2493 | h2493
                                  · rcases h5bigk with h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c | h2494c
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1241, hlam, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2436, h2437, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1490, hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2428, hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1241, hc01, hc15, hlam, hphi, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2432, h2436, h2437, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1487, h1489, h1490, h2430, h2434, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1487, h1489, h1490, h2430, h2433, h2435, h2441, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1488, hlam, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2432, hlam, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2437, hlam, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2439, hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1488, h2436, h2437, hc35, hlam, hphi, ht23, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2434, hlam, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2430, h2434, h2436, h2437, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2441, hlam, p2494_0]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h1488, h2430, h2433, h2435, h2436, h2437, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2435, hlam, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2430, h2433, h2435, h2436, h2437, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2494_1, u2ehi3]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [h2430, h2433, h2435, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2494_1]
                                    · have p2494_0 := h2494c.1
                                      have p2494_1 := h2494c.2.1
                                      have p2494_2 := h2494c.2.2.1
                                      have p2494_3 := h2494c.2.2.2
                                      linarith only [hlam, p2494_0]
                                  · linarith only [h2493, hlam, p2443_0]
                                · linarith only [h2435, h2492, hlam, p2443_1]
                              · linarith only [h2491, h927, hlam]
                            · linarith only [h0, h2490, hlam]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h2432, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h2434, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [h2435, hlam, p2443_0]
                        · have p2443_0 := h2443c.1
                          have p2443_1 := h2443c.2.1
                          have p2443_2 := h2443c.2.2.1
                          have p2443_3 := h2443c.2.2.2
                          linarith only [hlam, p2443_0]
                · linarith only [h1489, h2428, h2436, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2529 | h2529
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2530 | h2530
                  · linarith only [h0, h1486, h1490, h2530, h927, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2532 | h2532
                    · linarith only [h1487, h1489, h1490, h2434, h2435, h2532, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2534 | h2534
                      · linarith only [h1487, h1489, h1490, h2434, h2435, h2529, h2534, hc23, hlam, hphi, u2ehi3]
                      · rcases h1bigk with h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c | h2536c
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h0, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h927, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h1490, h2430, h2431, h2434, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2536_1, u2ehi3]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h1241, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          rcases p2536_3 (m.d 0 1) (by simp) with h2542 | h2542
                          · linarith only [h2542, hlam, p2536_0]
                          · rcases p2536_3 (m.d 1 2) (by simp) with h2544 | h2544
                            · rcases p2536_3 (m.d 1 3) (by simp) with h2545 | h2545
                              · linarith only [h2430, h2545, hlam]
                              · linarith only [h2545, h927, hlam]
                            · linarith only [h2544, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h1490, h2434, h927, hc01, hc12, hlam, hphi, p2536_1]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          rcases p2536_3 (m.d 0 1) (by simp) with h2551 | h2551
                          · linarith only [h0, h2551, hlam]
                          · rcases p2536_3 (m.d 1 2) (by simp) with h2553 | h2553
                            · rcases p2536_3 (m.d 1 3) (by simp) with h2554 | h2554
                              · linarith only [h2430, h2554, hlam]
                              · linarith only [h2433, h2554, hlam]
                            · linarith only [h2431, h2553, hlam]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h1487, h1489, h1490, h2434, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2536_1, u2ehi3]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          rcases p2536_3 (m.d 0 1) (by simp) with h2559 | h2559
                          · linarith only [h2559, hlam, p2536_0]
                          · rcases p2536_3 (m.d 1 2) (by simp) with h2561 | h2561
                            · rcases p2536_3 (m.d 1 3) (by simp) with h2562 | h2562
                              · rcases p2536_3 (m.d 1 4) (by simp) with h2563 | h2563
                                · linarith only [h2433, h2563, hlam]
                                · rcases p2536_3 (m.d 1 5) (by simp) with h2565 | h2565
                                  · linarith only [h2434, h2565, hlam]
                                  · linarith only [h1241, h2565, hlam]
                              · linarith only [h2562, hlam, p2536_0]
                            · linarith only [h0, h2561, hlam]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2430, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          rcases p2536_3 (m.d 0 1) (by simp) with h2572 | h2572
                          · linarith only [h2572, h927, hlam]
                          · rcases p2536_3 (m.d 1 2) (by simp) with h2574 | h2574
                            · rcases p2536_3 (m.d 1 3) (by simp) with h2575 | h2575
                              · rcases p2536_3 (m.d 1 4) (by simp) with h2576 | h2576
                                · linarith only [h2433, h2576, hlam]
                                · rcases p2536_3 (m.d 1 5) (by simp) with h2578 | h2578
                                  · linarith only [h2434, h2578, hlam]
                                  · linarith only [h2435, h2578, hlam]
                              · linarith only [h2433, h2575, hlam]
                            · linarith only [h2431, h2574, hlam]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h1487, h1489, h1490, h2434, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2536_1, u2ehi3]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2435, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2536_1]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2431, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2433, hlam, p2536_1]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2435, hlam, p2536_1]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          rcases p2536_3 (m.d 0 1) (by simp) with h2589 | h2589
                          · linarith only [h2589, hlam, p2536_0]
                          · rcases p2536_3 (m.d 1 2) (by simp) with h2591 | h2591
                            · rcases p2536_3 (m.d 1 3) (by simp) with h2592 | h2592
                              · rcases p2536_3 (m.d 1 4) (by simp) with h2593 | h2593
                                · linarith only [h2435, h2593, hlam]
                                · linarith only [h2431, h2435, h2593, hc45, hlam, hphi, ht23, ht34, p2536_1, u2ehi3]
                              · linarith only [h2592, h927, hlam]
                            · linarith only [h0, h2591, hlam]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2432, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2434, hlam, p2536_0]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [h2431, h2435, hc45, hlam, hphi, ht23, ht34, p2536_1, u2ehi3]
                        · have p2536_0 := h2536c.1
                          have p2536_1 := h2536c.2.1
                          have p2536_2 := h2536c.2.2.1
                          have p2536_3 := h2536c.2.2.2
                          linarith only [hlam, p2536_0]
                · linarith only [h1489, h1490, h2430, h2434, h2529, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2603 | h2603
              · linarith only [h1487, h2428, h2433, h2434, h2603, hc35, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2605 | h2605
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2606 | h2606
                  · linarith only [h1486, h2434, h2606, h927, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2608 | h2608
                    · linarith only [h1487, h2428, h2608, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2610 | h2610
                      · linarith only [h1486, h1487, h2428, h2434, h2605, h2610, h927, hc35, hlam, hphi, ht23, u2ehi3]
                      · rcases h1bigk with h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h0, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h927, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2431, h2434, h2610, h927, hc45, hlam, hphi, ht23, ht34, p2612_1, u2ehi3]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h1241, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          rcases p2612_3 (m.d 0 1) (by simp) with h2618 | h2618
                          · linarith only [h2618, hlam, p2612_0]
                          · rcases p2612_3 (m.d 1 2) (by simp) with h2620 | h2620
                            · rcases p2612_3 (m.d 1 3) (by simp) with h2621 | h2621
                              · linarith only [h2430, h2621, hlam]
                              · linarith only [h2621, h927, hlam]
                            · linarith only [h2620, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h927, hc01, hc12, hlam, hphi, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          rcases p2612_3 (m.d 0 1) (by simp) with h2627 | h2627
                          · linarith only [h0, h2627, hlam]
                          · rcases p2612_3 (m.d 1 2) (by simp) with h2629 | h2629
                            · rcases p2612_3 (m.d 1 3) (by simp) with h2630 | h2630
                              · linarith only [h2430, h2630, hlam]
                              · linarith only [h2433, h2630, hlam]
                            · linarith only [h2431, h2629, hlam]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2434, h927, hc01, hc12, hlam, hphi, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2434, hc01, hc35, hlam, hphi, ht12, ht23, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2430, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2431, h2434, h2610, hc45, hlam, hphi, ht23, ht34, p2612_1, u2ehi3]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2434, hlam, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2433, h2434, h2610, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2431, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2433, hlam, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2603, hlam, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          rcases p2612_3 (m.d 0 1) (by simp) with h2645 | h2645
                          · linarith only [h2645, hlam, p2612_0]
                          · rcases p2612_3 (m.d 1 2) (by simp) with h2647 | h2647
                            · rcases p2612_3 (m.d 1 3) (by simp) with h2648 | h2648
                              · linarith only [h2434, h2648, hlam]
                              · linarith only [h2648, h927, hlam]
                            · linarith only [h0, h2647, hlam]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2432, hlam, p2612_0]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h927, hc01, hc15, hlam, hphi, p2612_1]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [h2431, h2434, hc35, hlam, hphi, ht23, p2612_1, u2ehi3]
                        · have p2612_0 := h2612c.1
                          have p2612_1 := h2612c.2.1
                          have p2612_2 := h2612c.2.2.1
                          have p2612_3 := h2612c.2.2.2
                          linarith only [hlam, p2612_0]
                · linarith only [h1241, h1489, h1490, h2603, h2605, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h1489, h2433, h927, hlam]
        · linarith only [h0, h1486, h2432, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1486, h2431, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1486, h2430, hlam]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1489 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h1490 | h1490
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488 h1489 h1490
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488 h1489 h1490

end R2N4
