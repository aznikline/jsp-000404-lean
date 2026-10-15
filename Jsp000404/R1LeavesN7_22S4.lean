import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S2
import Jsp000404.R1LeavesN7_22S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x16 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 4) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 4) ∧ (m.d 0 2) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 2) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h2082 | h2082
  · rcases p1573_3 (m.d 0 2) (by simp) with h2083 | h2083
    · linarith only [h1385, h2083, hlam]
    · rcases p1573_3 (m.d 0 3) (by simp) with h2085 | h2085
      · rcases p1573_3 (m.d 0 4) (by simp) with h2086 | h2086
        · rcases p1573_3 (m.d 0 5) (by simp) with h2087 | h2087
          · linarith only [h1560, h2087, hlam]
          · rcases h0emin with h2089 | h2089 | h2089 | h2089 | h2089
            · rcases h2bigk with h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1558, h1565, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2090_1]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h4, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1385, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1558, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2090_1]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h0, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1561, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1563, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h0, h1558, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2090_1]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                rcases p2090_3 (m.d 0 2) (by simp) with h2101 | h2101
                · linarith only [h2101, hlam, p2090_0]
                · rcases p2090_3 (m.d 1 2) (by simp) with h2103 | h2103
                  · linarith only [h1561, h2103, hlam]
                  · rcases p2090_3 (m.d 2 3) (by simp) with h2105 | h2105
                    · rcases p2090_3 (m.d 2 4) (by simp) with h2106 | h2106
                      · linarith only [h1569, h2106, hlam]
                      · linarith only [h1385, h2106, hlam]
                    · linarith only [h2105, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                rcases p2090_3 (m.d 0 2) (by simp) with h2110 | h2110
                · linarith only [h2110, h4, hlam]
                · linarith only [h0, h2110, hlam]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1385, hc02, hc23, hlam, hphi, p1573_1, p2090_1]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h0, h1558, h1565, h4, hlam, p1573_1, p2090_2]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                rcases p2090_3 (m.d 0 2) (by simp) with h2116 | h2116
                · linarith only [h2116, hlam, p2090_0]
                · rcases p2090_3 (m.d 1 2) (by simp) with h2118 | h2118
                  · linarith only [h1563, h2118, hlam]
                  · rcases p2090_3 (m.d 2 3) (by simp) with h2120 | h2120
                    · rcases p2090_3 (m.d 2 4) (by simp) with h2121 | h2121
                      · rcases p2090_3 (m.d 2 5) (by simp) with h2122 | h2122
                        · linarith only [h1571, h2122, hlam]
                        · rcases h3bigk with h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1566, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h4, hlam, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            rcases p2124_3 (m.d 0 3) (by simp) with h2128 | h2128
                            · rcases p2124_3 (m.d 1 3) (by simp) with h2129 | h2129
                              · linarith only [h1, h2129, hlam]
                              · linarith only [h1566, h2129, hlam]
                            · linarith only [h2128, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, hlam, p1573_1, p2124_2]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1561, hlam, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            rcases p2124_3 (m.d 0 3) (by simp) with h2138 | h2138
                            · rcases p2124_3 (m.d 1 3) (by simp) with h2139 | h2139
                              · rcases p2124_3 (m.d 2 3) (by simp) with h2140 | h2140
                                · rcases p2124_3 (m.d 3 4) (by simp) with h2141 | h2141
                                  · linarith only [h1566, h2141, hlam]
                                  · linarith only [h1572, h2141, hlam]
                                · linarith only [h1570, h2140, hlam]
                              · linarith only [h2139, hlam, p2124_0]
                            · linarith only [h1559, h2138, hlam]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1566, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            rcases p2124_3 (m.d 0 3) (by simp) with h2150 | h2150
                            · linarith only [h2150, h4, hlam]
                            · linarith only [h1558, h2150, hlam]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, h4, hlam, p1573_1, p2124_2]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1558, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1566, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1569, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2124_1]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1559, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1567, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1570, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [h1572, hlam, p2124_0]
                          · have p2124_0 := h2124c.1
                            have p2124_1 := h2124c.2.1
                            have p2124_2 := h2124c.2.2.1
                            have p2124_3 := h2124c.2.2.2
                            linarith only [hlam, p2124_0]
                      · linarith only [h2121, hlam, p2090_0]
                    · linarith only [h2120, h4, hlam]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                rcases p2090_3 (m.d 0 2) (by simp) with h2166 | h2166
                · linarith only [h1385, h2166, hlam]
                · linarith only [h0, h2166, hlam]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1569, hlam, p2090_1]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h0, h1385, h1565, hlam, p1573_1, p2090_2]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1557, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1565, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1570, hlam, p2090_1]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [h1571, hlam, p2090_0]
              · have p2090_0 := h2090c.1
                have p2090_1 := h2090c.2.1
                have p2090_2 := h2090c.2.2.1
                have p2090_3 := h2090c.2.2.2
                linarith only [hlam, p2090_0]
            · linarith only [h1558, h2089, hc03, hlam, p1573_1]
            · rcases h2bigk with h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1558, h1565, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2178_1]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h4, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1385, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1558, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2178_1]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h0, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1561, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1563, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h0, h1558, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2178_1]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                rcases p2178_3 (m.d 0 2) (by simp) with h2189 | h2189
                · linarith only [h2189, hlam, p2178_0]
                · rcases p2178_3 (m.d 1 2) (by simp) with h2191 | h2191
                  · linarith only [h1561, h2191, hlam]
                  · rcases p2178_3 (m.d 2 3) (by simp) with h2193 | h2193
                    · rcases p2178_3 (m.d 2 4) (by simp) with h2194 | h2194
                      · linarith only [h1569, h2194, hlam]
                      · linarith only [h1385, h2194, hlam]
                    · linarith only [h2193, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                rcases p2178_3 (m.d 0 2) (by simp) with h2198 | h2198
                · linarith only [h2198, h4, hlam]
                · linarith only [h0, h2198, hlam]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1385, hc02, hc23, hlam, hphi, p1573_1, p2178_1]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h0, h1558, h1565, h4, hlam, p1573_1, p2178_2]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                rcases p2178_3 (m.d 0 2) (by simp) with h2204 | h2204
                · linarith only [h2204, hlam, p2178_0]
                · rcases p2178_3 (m.d 1 2) (by simp) with h2206 | h2206
                  · linarith only [h1563, h2206, hlam]
                  · rcases p2178_3 (m.d 2 3) (by simp) with h2208 | h2208
                    · rcases p2178_3 (m.d 2 4) (by simp) with h2209 | h2209
                      · rcases p2178_3 (m.d 2 5) (by simp) with h2210 | h2210
                        · linarith only [h1571, h2210, hlam]
                        · rcases h3bigk with h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1566, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h4, hlam, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            rcases p2212_3 (m.d 0 3) (by simp) with h2216 | h2216
                            · rcases p2212_3 (m.d 1 3) (by simp) with h2217 | h2217
                              · linarith only [h1, h2217, hlam]
                              · linarith only [h1566, h2217, hlam]
                            · linarith only [h2216, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, hlam, p1573_1, p2212_2]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1561, hlam, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            rcases p2212_3 (m.d 0 3) (by simp) with h2226 | h2226
                            · rcases p2212_3 (m.d 1 3) (by simp) with h2227 | h2227
                              · rcases p2212_3 (m.d 2 3) (by simp) with h2228 | h2228
                                · rcases p2212_3 (m.d 3 4) (by simp) with h2229 | h2229
                                  · linarith only [h1566, h2229, hlam]
                                  · linarith only [h1572, h2229, hlam]
                                · linarith only [h1570, h2228, hlam]
                              · linarith only [h2227, hlam, p2212_0]
                            · linarith only [h1559, h2226, hlam]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1566, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            rcases p2212_3 (m.d 0 3) (by simp) with h2238 | h2238
                            · linarith only [h2238, h4, hlam]
                            · linarith only [h1558, h2238, hlam]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, h4, hlam, p1573_1, p2212_2]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1558, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1566, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1569, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2212_1]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1559, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1567, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1570, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [h1572, hlam, p2212_0]
                          · have p2212_0 := h2212c.1
                            have p2212_1 := h2212c.2.1
                            have p2212_2 := h2212c.2.2.1
                            have p2212_3 := h2212c.2.2.2
                            linarith only [hlam, p2212_0]
                      · linarith only [h2209, hlam, p2178_0]
                    · linarith only [h2208, h4, hlam]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                rcases p2178_3 (m.d 0 2) (by simp) with h2254 | h2254
                · linarith only [h1385, h2254, hlam]
                · linarith only [h0, h2254, hlam]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1569, hlam, p2178_1]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h0, h1385, h1565, hlam, p1573_1, p2178_2]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1557, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1565, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1570, hlam, p2178_1]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [h1571, hlam, p2178_0]
              · have p2178_0 := h2178c.1
                have p2178_1 := h2178c.2.1
                have p2178_2 := h2178c.2.2.1
                have p2178_3 := h2178c.2.2.2
                linarith only [hlam, p2178_0]
            · rcases h2bigk with h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1558, h1565, h1570, h1572, hc03, hc45, hlam, hphi, ht0b, ht5b, p1573_1, p2265_1]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h4, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1385, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1558, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2265_1]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h0, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1561, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1563, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h0, h1558, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2265_1]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                rcases p2265_3 (m.d 0 2) (by simp) with h2276 | h2276
                · linarith only [h2276, hlam, p2265_0]
                · rcases p2265_3 (m.d 1 2) (by simp) with h2278 | h2278
                  · linarith only [h1561, h2278, hlam]
                  · rcases p2265_3 (m.d 2 3) (by simp) with h2280 | h2280
                    · rcases p2265_3 (m.d 2 4) (by simp) with h2281 | h2281
                      · linarith only [h1569, h2281, hlam]
                      · linarith only [h1385, h2281, hlam]
                    · linarith only [h2280, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                rcases p2265_3 (m.d 0 2) (by simp) with h2285 | h2285
                · linarith only [h2285, h4, hlam]
                · linarith only [h0, h2285, hlam]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1385, hc02, hc23, hlam, hphi, p1573_1, p2265_1]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h0, h1558, h1565, h4, hlam, p1573_1, p2265_2]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                rcases p2265_3 (m.d 0 2) (by simp) with h2291 | h2291
                · linarith only [h2291, hlam, p2265_0]
                · rcases p2265_3 (m.d 1 2) (by simp) with h2293 | h2293
                  · linarith only [h1563, h2293, hlam]
                  · rcases p2265_3 (m.d 2 3) (by simp) with h2295 | h2295
                    · rcases p2265_3 (m.d 2 4) (by simp) with h2296 | h2296
                      · rcases p2265_3 (m.d 2 5) (by simp) with h2297 | h2297
                        · linarith only [h1571, h2297, hlam]
                        · rcases h3bigk with h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c | h2299c
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1566, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h4, hlam, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            rcases p2299_3 (m.d 0 3) (by simp) with h2303 | h2303
                            · rcases p2299_3 (m.d 1 3) (by simp) with h2304 | h2304
                              · linarith only [h1, h2304, hlam]
                              · linarith only [h1566, h2304, hlam]
                            · linarith only [h2303, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, hlam, p1573_1, p2299_2]
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
                            linarith only [h1561, hlam, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            rcases p2299_3 (m.d 0 3) (by simp) with h2313 | h2313
                            · rcases p2299_3 (m.d 1 3) (by simp) with h2314 | h2314
                              · rcases p2299_3 (m.d 2 3) (by simp) with h2315 | h2315
                                · rcases p2299_3 (m.d 3 4) (by simp) with h2316 | h2316
                                  · linarith only [h1566, h2316, hlam]
                                  · linarith only [h1572, h2316, hlam]
                                · linarith only [h1570, h2315, hlam]
                              · linarith only [h2314, hlam, p2299_0]
                            · linarith only [h1559, h2313, hlam]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1566, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            rcases p2299_3 (m.d 0 3) (by simp) with h2325 | h2325
                            · linarith only [h2325, h4, hlam]
                            · linarith only [h1558, h2325, hlam]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h0, h1558, h1565, h1570, h4, hlam, p1573_1, p2299_2]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1558, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1566, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1569, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2299_1]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1559, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1567, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1570, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [h1572, hlam, p2299_0]
                          · have p2299_0 := h2299c.1
                            have p2299_1 := h2299c.2.1
                            have p2299_2 := h2299c.2.2.1
                            have p2299_3 := h2299c.2.2.2
                            linarith only [hlam, p2299_0]
                      · linarith only [h2296, hlam, p2265_0]
                    · linarith only [h2295, h4, hlam]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                rcases p2265_3 (m.d 0 2) (by simp) with h2341 | h2341
                · linarith only [h1385, h2341, hlam]
                · linarith only [h0, h2341, hlam]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1569, hlam, p2265_1]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h0, h1385, h1565, hlam, p1573_1, p2265_2]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1557, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1565, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1570, hlam, p2265_1]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [h1571, hlam, p2265_0]
              · have p2265_0 := h2265c.1
                have p2265_1 := h2265c.2.1
                have p2265_2 := h2265c.2.2.1
                have p2265_3 := h2265c.2.2.2
                linarith only [hlam, p2265_0]
            · linarith only [h2089, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
        · linarith only [h1385, h2086, hlam]
      · linarith only [h2085, h4, hlam]
  · linarith only [h0, h2082, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x17 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 4) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 4) ∧ (m.d 0 3) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 3) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1558, hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x18 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 4) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 4) ∧ (m.d 0 4) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 4) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x19 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 4) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 4) ∧ (m.d 0 5) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 5) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h2358 | h2358
  · rcases p1573_3 (m.d 0 2) (by simp) with h2359 | h2359
    · linarith only [h1385, h2359, hlam]
    · linarith only [h1557, h2359, hlam]
  · linarith only [h2358, h3, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x20 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 5) ∧ (m.d 0 1) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 1) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h3, hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x21 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 5) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 5) ∧ (m.d 0 2) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 2) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1557, hlam, p1573_1]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x22 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 5) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 5) ∧ (m.d 0 3) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 3) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1559, hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x23 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 5) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 5) ∧ (m.d 0 4) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 4) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1560, hlam, p1573_1]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x24 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 5) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 5) ∧ (m.d 0 5) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 5) ≤ z)))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases h0bigk with h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x2 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x3 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x4 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x5 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x6 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x7 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x8 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x9 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x10 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x11 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x12 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x13 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x14 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x15 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x16 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x17 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x18 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x19 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x20 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x21 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x22 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x23 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x24 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572 h1573c

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1572, hc34, hlam, hphi, ht45, u5elo4]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 3 4 5 (by decide) (by decide) with h1572 | h1572
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571 h1572

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1385, h1571, hc04, hlam, hphi, ht45, u5elo4]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 2 4 5 (by decide) (by decide) with h1571 | h1571
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570 h1571

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1570, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 2 3 5 (by decide) (by decide) with h1570 | h1570
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569 h1570

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1558, h1569, h4, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 2 3 4 (by decide) (by decide) with h1569 | h1569
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568 h1569

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1568, hc14, hlam, hphi, ht45, u5elo4]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 4 5 (by decide) (by decide) with h1568 | h1568
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567 h1568

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1567, hc13, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 3 5 (by decide) (by decide) with h1567 | h1567
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566 h1567

end R2N4
